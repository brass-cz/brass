//! Message digests and HMAC, as a native Brass plugin.
//!
//! `std/hash.cz` owns the user-facing API (the typed one-shot functions,
//! the `Hasher` handle, hex rendering, the constant-time compare) and calls in
//! here for the digests themselves. They are RustCrypto implementations rather
//! than Brass code: every one of these algorithms is built from wrapping
//! 32/64-bit arithmetic, which Brass does not have (and which the JIT leaves
//! undefined on overflow), so a Brass implementation would be a hand-masked
//! emulation whose failure mode is a silently wrong digest.
//!
//! One function per algorithm, rather than one function taking an algorithm
//! name: a digest cannot fail, and a name-keyed entry point would have to
//! report an unknown name -- making every call fallible on the Brass side for
//! an error the typed wrapper can never produce.
//!
//! Streaming state (a partially-fed hasher) is not a value the plugin ABI can
//! carry, so it lives in a process-wide handle table and the `hasher_*`
//! functions take an `i64` handle -- the same shape the net library's TLS
//! sessions use. There the algorithm IS chosen by name (the handle is minted
//! once, and the call is fallible anyway).

use std::sync::OnceLock;

use brass_plugin::{BrassLib, Bytes, HandleError, HandleTable, Registry, brass_lib, decl, export};
use digest::{Digest, DynDigest};
use hmac::{Hmac, KeyInit, Mac};

/// The digest of `data` under `D`.
fn digest_of<D: Digest>(data: &[u8]) -> Bytes {
    let mut d = D::new();
    d.update(data);
    Bytes(d.finalize().to_vec())
}

/// The HMAC of `data` keyed by `key`, over the inner hash named by the type
/// argument. A macro rather than a generic function: HMAC's key schedule needs
/// the inner hash's block size at the type level, and spelling that bound out
/// (`EagerHash` + its supertraits) says less than the expansion it guards.
///
/// HMAC is defined for a key of ANY length -- it hashes a key longer than the
/// block size and zero-pads a shorter one -- so `new_from_slice` cannot fail
/// here (pinned by `hmac_accepts_any_key_length`); the `expect` says so rather
/// than propagating an error the Brass side would have to handle. A plugin
/// panic is caught at the ABI boundary and surfaces as a call error, so even a
/// wrong assumption here cannot corrupt the runtime.
macro_rules! hmac_of {
    ($d:ty, $key:expr, $data:expr) => {{
        let mut m =
            <Hmac<$d> as KeyInit>::new_from_slice($key).expect("HMAC accepts a key of any length");
        m.update($data);
        Bytes(m.finalize().into_bytes().to_vec())
    }};
}

/// A fresh, empty streaming hasher for `alg`. Boxed as a `DynDigest` so one
/// handle table serves every algorithm; the concrete types differ only in
/// their state.
fn new_digest(alg: &str) -> Result<Box<dyn DynDigest + Send>, String> {
    Ok(match alg {
        "md5" => Box::new(md5::Md5::default()),
        "sha1" => Box::new(sha1::Sha1::default()),
        "sha224" => Box::new(sha2::Sha224::default()),
        "sha256" => Box::new(sha2::Sha256::default()),
        "sha384" => Box::new(sha2::Sha384::default()),
        "sha512" => Box::new(sha2::Sha512::default()),
        other => {
            return Err(format!(
                "unknown hash algorithm `{other}` (known: md5, sha1, sha224, sha256, sha384, sha512)"
            ));
        }
    })
}

export! {
    /// The MD5 digest of `data` (16 bytes).
    fn hash_md5(data: Bytes) -> Bytes {
        digest_of::<md5::Md5>(&data.0)
    }

    /// The SHA-1 digest of `data` (20 bytes).
    fn hash_sha1(data: Bytes) -> Bytes {
        digest_of::<sha1::Sha1>(&data.0)
    }

    /// The SHA-224 digest of `data` (28 bytes).
    fn hash_sha224(data: Bytes) -> Bytes {
        digest_of::<sha2::Sha224>(&data.0)
    }

    /// The SHA-256 digest of `data` (32 bytes).
    fn hash_sha256(data: Bytes) -> Bytes {
        digest_of::<sha2::Sha256>(&data.0)
    }

    /// The SHA-384 digest of `data` (48 bytes).
    fn hash_sha384(data: Bytes) -> Bytes {
        digest_of::<sha2::Sha384>(&data.0)
    }

    /// The SHA-512 digest of `data` (64 bytes).
    fn hash_sha512(data: Bytes) -> Bytes {
        digest_of::<sha2::Sha512>(&data.0)
    }

    /// The HMAC-SHA-1 of `data` keyed by `key` (20 bytes).
    fn hmac_sha1(key: Bytes, data: Bytes) -> Bytes {
        hmac_of!(sha1::Sha1, &key.0, &data.0)
    }

    /// The HMAC-SHA-256 of `data` keyed by `key` (32 bytes).
    fn hmac_sha256(key: Bytes, data: Bytes) -> Bytes {
        hmac_of!(sha2::Sha256, &key.0, &data.0)
    }

    /// The HMAC-SHA-512 of `data` keyed by `key` (64 bytes).
    fn hmac_sha512(key: Bytes, data: Bytes) -> Bytes {
        hmac_of!(sha2::Sha512, &key.0, &data.0)
    }

    /// Start a streaming hasher for `alg` and return its handle. The handle
    /// owns the hasher's state until `hasher_finalize` consumes it, so a hasher
    /// that is never finalized holds its state (a few hundred bytes) for the
    /// life of the process.
    fn hasher_new(alg: String) -> Result<i64, String> {
        let digest = new_digest(&alg)?;
        table().insert(digest).map_err(handle_error)
    }

    /// Feed `data` to the hasher. Digests are streaming, so one array of N
    /// bytes and N arrays of one byte produce the same digest.
    fn hasher_update(handle: i64, data: Bytes) -> Result<(), String> {
        table()
            .with_mut(handle, |digest| digest.update(&data.0))
            .map_err(handle_error)
    }

    /// The digest of everything fed to the hasher so far, CONSUMING it: the
    /// handle is released, and any later use of it is an error. (A digest is
    /// not resumable after finalization, so keeping the handle alive would only
    /// offer a broken second call.)
    fn hasher_finalize(handle: i64) -> Result<Bytes, String> {
        let digest = table().remove(handle).map_err(handle_error)?;
        Ok(Bytes(digest.finalize().to_vec()))
    }
}

/// Live streaming hashers by handle. Each hasher is owned by exactly one
/// Brass `Hasher` value, so the map lock is only ever held for one update --
/// there is no per-hasher lock as the TLS session table needs.
type HasherTable = HandleTable<Box<dyn DynDigest + Send>>;

fn table() -> &'static HasherTable {
    static TABLE: OnceLock<HasherTable> = OnceLock::new();
    TABLE.get_or_init(HandleTable::new)
}

fn handle_error(error: HandleError) -> String {
    match error {
        HandleError::Poisoned => "the hasher table is poisoned".to_string(),
        HandleError::Exhausted => "the hasher table cannot allocate another handle".to_string(),
        HandleError::Missing(_) => "this hasher was already finalized".to_string(),
    }
}

struct HashLib;

impl BrassLib for HashLib {
    fn entry(reg: &mut Registry) {
        reg.export(decl!(hash_md5));
        reg.export(decl!(hash_sha1));
        reg.export(decl!(hash_sha224));
        reg.export(decl!(hash_sha256));
        reg.export(decl!(hash_sha384));
        reg.export(decl!(hash_sha512));
        reg.export(decl!(hmac_sha1));
        reg.export(decl!(hmac_sha256));
        reg.export(decl!(hmac_sha512));
        reg.export(decl!(hasher_new));
        reg.export(decl!(hasher_update));
        reg.export(decl!(hasher_finalize));
    }
}

brass_lib!(HashLib);

#[cfg(test)]
mod tests {
    use super::*;

    fn hex(b: &[u8]) -> String {
        b.iter().map(|x| format!("{x:02x}")).collect()
    }

    /// The published vectors for each algorithm: RFC 1321 (MD5), RFC 3174
    /// (SHA-1), and FIPS 180-4 (SHA-2), all for the message "abc". A wrong
    /// digest is indistinguishable from a right one by inspection, so the
    /// vectors are the only real check.
    #[test]
    fn digests_match_the_published_vectors() {
        let cases = [
            ("md5", "900150983cd24fb0d6963f7d28e17f72"),
            ("sha1", "a9993e364706816aba3e25717850c26c9cd0d89d"),
            (
                "sha224",
                "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7",
            ),
            (
                "sha256",
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
            ),
            (
                "sha384",
                "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed\
                 8086072ba1e7cc2358baeca134c825a7",
            ),
            (
                "sha512",
                "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a\
                 2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f",
            ),
        ];
        for (alg, want) in cases {
            // Through the streaming path, which is the one the export'd
            // one-shot functions do NOT share -- so both are covered.
            let mut d = new_digest(alg).expect(alg);
            d.update(b"abc");
            assert_eq!(hex(&d.finalize()), want, "streaming {alg} of \"abc\"");
        }
        assert_eq!(hex(&digest_of::<md5::Md5>(b"abc").0), cases[0].1);
        assert_eq!(hex(&digest_of::<sha2::Sha256>(b"abc").0), cases[3].1);
    }

    /// RFC 4231 test case 2 (key "Jefe"): pins that the key schedule, not just
    /// the inner hash, is right.
    #[test]
    fn hmac_matches_rfc_4231() {
        let mac = hmac_of!(sha2::Sha256, b"Jefe", b"what do ya want for nothing?");
        assert_eq!(
            hex(&mac.0),
            "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
        );
    }

    /// HMAC is defined for any key length, which is what lets `hmac_of` treat
    /// the key check as infallible: an empty key and one far longer than the
    /// block size must both produce a digest rather than an error.
    #[test]
    fn hmac_accepts_any_key_length() {
        for len in [0usize, 1, 64, 65, 1000] {
            let key = vec![0xa5u8; len];
            let mac = hmac_of!(sha2::Sha256, &key, b"m");
            assert_eq!(mac.0.len(), 32, "key of {len} bytes");
        }
    }
}
