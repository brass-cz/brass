#!/bin/bash -e

set -euo pipefail

# Run the packaged czpm from a moved copy of the staging tree: the toolchain
# must resolve its standard library and native plugins relative to the
# installed binary, never through the staging path.
verify_relocated_toolchain() {
    local staging=$1
    local relocated
    local run_stderr
    local failed=0

    relocated=$(mktemp -d "$(dirname "$staging")/.brass-relocation.XXXXXX")
    rmdir "$relocated"
    mv "$staging" "$relocated"
    run_stderr="$relocated/.relocation-run.stderr"
    if ! env -u BRASS_INCLUDE -u BRASS_PACKAGES \
        PATH="$relocated/bin:$PATH" \
        "$relocated/bin/czpm" help >/dev/null 2>"$run_stderr"; then
        echo "relocated czpm smoke failed:" >&2
        sed -n '1,120p' "$run_stderr" >&2
        failed=1
    fi
    rm -f -- "$run_stderr"
    if ! mv "$relocated" "$staging"; then
        echo "failed to restore staging tree from relocation smoke: $relocated" >&2
        return 1
    fi
    return "$failed"
}

cd "$(dirname "$0")/../"
cwd="$(pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' 0
artifact="$cwd/brass-$(rustc --print=host-tuple).tar.gz"

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

env -u BRASS_INCLUDE -u BRASS_PACKAGES "$tmp/bin/brass" check "$tmp/bin/czpm"
verify_relocated_toolchain "$tmp"

#
# make tarball
#

cd "$tmp"
tar czf "$artifact" bin std

cd "$cwd"
