#!/bin/bash -e

set -euo pipefail

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
