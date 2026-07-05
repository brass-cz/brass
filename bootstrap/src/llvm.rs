use anyhow::{Context as _, bail};
use sha2::{Digest, Sha256};
use std::{env, ffi::OsString, fs, path::Path, process::Command};
use tar::Archive;
use xz::read::XzDecoder;

pub const LLVM_VERSION: &str = "22.1.0";
pub const LLVM_SYS_ENV: &str = "LLVM_SYS_221_PREFIX";

/// Pinned SHA-256 of each prebuilt LLVM release archive, keyed by asset file
/// name, from the GitHub release's published asset digests. A download is
/// rejected unless its bytes hash to the pinned value, so a tampered mirror, a
/// swapped redirect, or a corrupted transfer cannot be linked into the compiler.
/// Bumping `LLVM_VERSION` requires adding the new archives' digests here -- an
/// asset with no pinned digest is refused, not trusted. (LLVM 22.1.0 ships no
/// macOS-x86_64 archive, so none is listed.)
const LLVM_SHA256: &[(&str, &str)] = &[
    (
        "LLVM-22.1.0-Linux-ARM64.tar.xz",
        "e3b4205fe45d5561dec9d46465873a79c26b25b028b310515b38c34f668c6aec",
    ),
    (
        "LLVM-22.1.0-Linux-X64.tar.xz",
        "8d662e425e46c48b45f5f970770b5e37f323607c8c2cbc371593fc9c4ba1e7b3",
    ),
    (
        "LLVM-22.1.0-macOS-ARM64.tar.xz",
        "cd5e615f4dab23d0239359cd343202c5f6ceeaf072c245a3c685d73afac09646",
    ),
];

/// Download, integrity-check, and unpack LLVM into `dest`.
pub async fn download_llvm(dest: impl AsRef<Path>) -> anyhow::Result<()> {
    let dest = dest.as_ref();
    let asset = asset_name()?;
    let data = crate::http::download(asset.clone(), llvm_url(&asset)).await?;
    verify_digest(&asset, &data)?;
    extract(&data, dest)
}

/// Configure child processes so release builds link the downloaded LLVM with a
/// matching LTO plugin. The official macOS LLVM 22 archives contain bitcode
/// members in their static libraries; when Cargo's release profile enables LTO,
/// Apple's default linker otherwise asks Xcode's older `libLTO.dylib` to read
/// those members and fails before the final executable is produced.
pub fn configure_linker(cmd: &mut Command, llvm_path: &Path) {
    if cfg!(target_os = "macos") {
        let lto = llvm_path.join("lib").join("libLTO.dylib");
        if lto.is_file() {
            append_rustflag(
                cmd,
                format!("-Clink-arg=-Wl,-lto_library,{}", lto.display()),
            );
        }
    }
}

fn append_rustflag(cmd: &mut Command, flag: String) {
    if env::var_os("CARGO_ENCODED_RUSTFLAGS").is_some() {
        cmd.env(
            "CARGO_ENCODED_RUSTFLAGS",
            appended_env("CARGO_ENCODED_RUSTFLAGS", "\x1f", &flag),
        );
    } else {
        cmd.env("RUSTFLAGS", appended_env("RUSTFLAGS", " ", &flag));
    }
}

fn appended_env(name: &str, separator: &str, value: &str) -> OsString {
    let mut values = env::var_os(name).unwrap_or_default();
    if !values.is_empty() {
        values.push(separator);
    }
    values.push(value);
    values
}

/// The release archive file name for the host OS/architecture.
fn asset_name() -> anyhow::Result<String> {
    Ok(format!(
        "LLVM-{LLVM_VERSION}-{}-{}.tar.xz",
        get_os_repr()?,
        get_target_repr()?
    ))
}

fn llvm_url(asset: &str) -> String {
    format!("https://github.com/llvm/llvm-project/releases/download/llvmorg-{LLVM_VERSION}/{asset}")
}

/// Reject the download unless its SHA-256 matches the digest pinned for `asset`.
fn verify_digest(asset: &str, data: &[u8]) -> anyhow::Result<()> {
    let expected = LLVM_SHA256
        .iter()
        .find(|(name, _)| *name == asset)
        .map(|(_, d)| *d)
        .with_context(|| format!("no pinned SHA-256 for `{asset}` (update LLVM_SHA256)"))?;
    let actual = hex(Sha256::digest(data).as_slice());
    if actual != expected {
        bail!("LLVM archive `{asset}` failed integrity check: expected {expected}, got {actual}");
    }
    Ok(())
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Unpack the `.tar.xz` into `dest`, keeping the flattened layout: the archive's
/// single top-level directory becomes `dest`. The archive is expanded with
/// `tar::Archive::unpack` (into a sibling staging dir), which validates that every
/// entry -- including symlink and hardlink targets -- stays inside the
/// destination; the top directory is then promoted. A previous version joined the
/// path by hand and called the unchecked `Entry::unpack`, which a crafted `../` or
/// symlink entry could use to write outside `dest` (a tar-slip).
fn extract(data: &[u8], dest: &Path) -> anyhow::Result<()> {
    let staging = dest.with_extension("download.tmp");
    if staging.exists() {
        fs::remove_dir_all(&staging).context("clearing the LLVM staging dir")?;
    }
    Archive::new(XzDecoder::new(data))
        .unpack(&staging)
        .context("failed to unpack LLVM")?;
    let top = fs::read_dir(&staging)
        .context("reading the LLVM staging dir")?
        .filter_map(Result::ok)
        .map(|e| e.path())
        .find(|p| p.is_dir())
        .context("LLVM archive had no top-level directory")?;
    fs::rename(&top, dest).context("installing LLVM")?;
    let _ = fs::remove_dir_all(&staging);
    Ok(())
}

fn get_os_repr() -> anyhow::Result<&'static str> {
    if cfg!(target_os = "linux") {
        Ok("Linux")
    } else if cfg!(target_os = "macos") {
        Ok("macOS")
    } else {
        anyhow::bail!("unsupported OS")
    }
}

fn get_target_repr() -> anyhow::Result<&'static str> {
    if cfg!(target_arch = "aarch64") {
        Ok("ARM64")
    } else if cfg!(target_arch = "x86_64") {
        Ok("X64")
    } else {
        anyhow::bail!("unsupported arch")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sha256_hex_matches_known_vector() {
        // SHA-256 of the empty input, a standard published test vector.
        assert_eq!(
            hex(Sha256::digest(b"").as_slice()),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    #[test]
    fn pinned_digests_are_well_formed() {
        for (name, digest) in LLVM_SHA256 {
            assert!(name.ends_with(".tar.xz"), "{name}");
            assert_eq!(digest.len(), 64, "{name}");
            assert!(digest.bytes().all(|b| b.is_ascii_hexdigit()), "{name}");
        }
    }

    #[test]
    fn a_tampered_archive_is_rejected() {
        assert!(verify_digest("LLVM-22.1.0-Linux-ARM64.tar.xz", b"not the real bytes").is_err());
    }
}
