#!/bin/bash -e

set -euo pipefail

verify_relocated_artifacts() {
    local staging=$1
    local parent
    local relocated
    local analysis_cache="bin/czpm.czcache"
    local object_cache="bin/czpm.o2.czobj"
    local analysis_inode
    local object_inode
    local failed=0

    parent=$(dirname "$staging")
    relocated=$(mktemp -d "$parent/.brass-relocation.XXXXXX")
    rmdir "$relocated"
    analysis_inode=$(ls -di -- "$staging/$analysis_cache" | awk '{print $1}')
    object_inode=$(ls -di -- "$staging/$object_cache" | awk '{print $1}')
    mv "$staging" "$relocated"

    local run_xdg="$relocated/.relocation-run-xdg"
    local run_stdout="$relocated/.relocation-run.stdout"
    local run_stderr="$relocated/.relocation-run.stderr"
    if ! env -u BRASS_INCLUDE -u BRASS_PACKAGES \
        BRASS_LOG=brass::perf=debug \
        PATH="$relocated/bin:$PATH" \
        XDG_CACHE_HOME="$run_xdg" \
        "$relocated/bin/czpm" help >"$run_stdout" 2>"$run_stderr"; then
        echo "relocated czpm smoke failed:" >&2
        sed -n '1,120p' "$run_stderr" >&2
        failed=1
    elif ! grep -q 'front/cache-hit' "$run_stderr"; then
        echo "relocated czpm regenerated its analysis instead of using the shipped cache" >&2
        sed -n '1,120p' "$run_stderr" >&2
        failed=1
    fi

    local probe_dir="$relocated/.relocation-seed-probe"
    local probe_xdg="$relocated/.relocation-seed-xdg"
    local probe_stderr="$relocated/.relocation-seed.stderr"
    mkdir -p "$probe_dir"
    cp "$relocated/bin/czpm" "$probe_dir/czpm"
    if ! env -u BRASS_INCLUDE -u BRASS_PACKAGES \
        BRASS_LOG=brass::perf=debug \
        XDG_CACHE_HOME="$probe_xdg" \
        "$relocated/bin/brass" check "$probe_dir/czpm" 2>"$probe_stderr"; then
        echo "relocated shipped-context smoke failed:" >&2
        sed -n '1,120p' "$probe_stderr" >&2
        failed=1
    elif ! grep -q 'context seed loaded from disk' "$probe_stderr"; then
        echo "relocated driver did not load a shipped context seed with an empty XDG cache" >&2
        sed -n '1,120p' "$probe_stderr" >&2
        failed=1
    fi

    if [[ $(ls -di -- "$relocated/$analysis_cache" | awk '{print $1}') != "$analysis_inode" ]]; then
        echo "relocated czpm rewrote its shipped analysis cache" >&2
        failed=1
    fi
    if [[ $(ls -di -- "$relocated/$object_cache" | awk '{print $1}') != "$object_inode" ]]; then
        echo "relocated czpm rewrote its shipped native-object cache" >&2
        failed=1
    fi

    rm -rf -- "$run_xdg" "$run_stdout" "$run_stderr" \
        "$probe_dir" "$probe_xdg" "$probe_stderr"
    if ! mv "$relocated" "$staging"; then
        echo "failed to restore staging tree from relocation smoke: $relocated" >&2
        return 1
    fi
    if [[ "$failed" -ne 0 ]]; then
        return 1
    fi
    echo "relocation smoke: shipped czpm caches and context seeds loaded after moving the tree"
}

generate_precompiled_artifacts() {
    local staging=$1
    local brass="$staging/bin/brass"
    local cache_xdg="$staging/cache-xdg"
    local version

    if [[ "$staging" == / || ! -x "$brass" ]]; then
        echo "invalid Brass staging tree: $staging" >&2
        return 1
    fi
    mkdir -p "$staging/cache"
    version=$("$brass" --version)
    if [[ "$version" == *"(nightly "* ]]; then
        echo "warning: $version is not release-stamped; skipping shipped cache generation" >&2
        return 0
    fi
    if [[ -e "$cache_xdg" ]]; then
        echo "refusing to reuse artifact cache workspace: $cache_xdg" >&2
        return 1
    fi

    local entry
    for entry in "$staging/bin/czpm" "$staging/std/package_manager/fetch.cz"; do
        env -u BRASS_INCLUDE -u BRASS_PACKAGES \
            XDG_CACHE_HOME="$cache_xdg" \
            "$brass" check "$entry"

        env -u BRASS_INCLUDE -u BRASS_PACKAGES \
            BRASS_OPT=2 BRASS_JIT_CPU=generic BRASS_OBJ_PRECOMPILE=all \
            XDG_CACHE_HOME="$cache_xdg" \
            "$brass" "$entry" help

        local stem=$entry
        [[ "$entry" == *.cz ]] && stem=${entry%.cz}
        [[ -f "$stem.czcache" ]] || {
            echo "missing generated analysis cache: $stem.czcache" >&2
            return 1
        }
        [[ -f "$stem.o2.czobj" ]] || {
            echo "missing generated native-object cache: $stem.o2.czobj" >&2
            return 1
        }
    done

    local seed_count=0
    while IFS= read -r -d '' seed; do
        mv "$seed" "$staging/cache/"
        seed_count=$((seed_count + 1))
    done < <(find "$cache_xdg/brass" -maxdepth 1 -type f -name '*.czctx' -print0)
    if [[ "$seed_count" == 0 ]]; then
        echo "no context seeds were generated" >&2
        return 1
    fi
    rm -rf -- "$cache_xdg"
    verify_relocated_artifacts "$staging"
}

if [[ "${1:-}" == "--artifacts-only" ]]; then
    if [[ $# -ne 2 ]]; then
        echo "usage: $0 --artifacts-only STAGING_DIR" >&2
        exit 2
    fi
    staging=$(cd "$2" && pwd)
    generate_precompiled_artifacts "$staging"
    exit
elif [[ $# -ne 0 ]]; then
    echo "usage: $0 [--artifacts-only STAGING_DIR]" >&2
    exit 2
fi

cd "$(dirname "$0")/../"
cwd="$(pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' 0
artifact="$cwd/brass-$(rustc --print=host-tuple).tar.gz"
if [[ -e "$artifact" ]]; then
    echo "refusing to overwrite existing artifact: $artifact" >&2
    exit 1
fi

./x cargo install --path crates/brass_driver --root "$tmp"
./x cargo install --path crates/brass_language_server --root "$tmp"
./x cargo install --path crates/brass_formatter --root "$tmp"

#
# Brass scripts
#
czpm_path="$tmp/bin/czpm"
cat << CZPM > "$czpm_path"
#!/usr/bin/env brass

import std.package_manager.exec.main

main()!
CZPM
chmod +x "$czpm_path"

#
# standard library
#

./std/build.sh release

for path in $(find std -type f | grep -E '\.(cz|so|dylib|dll)$'); do
    mkdir -p "$tmp/$(dirname "$path")"
    cp "$path" "$tmp/$path"
done

generate_precompiled_artifacts "$tmp"

#
# make tarball
#

cd "$tmp"
tar czf "$artifact" bin std cache

cd "$cwd"
