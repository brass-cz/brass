#!/bin/bash -e

set -euo pipefail

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
#!/usr/bin/env -S brass --

import std.package_manager.exec.main

main()
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

#
# make tarball
#

cd "$tmp"
tar czf "$artifact" bin std

cd "$cwd"
