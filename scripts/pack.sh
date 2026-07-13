#!/bin/bash -e

cd "$(dirname "$0")/../"
cwd="$(pwd)"
tmp="$(mktemp -d)"

./x cargo install --path crates/prepoly_driver --root "$tmp"
./x cargo install --path crates/prepoly_language_server --root "$tmp"
./x cargo install --path crates/prepoly_formatter --root "$tmp"

#
# prepoly scripts
#
ppm_path="$tmp/bin/ppm"
cat << PPM > "$ppm_path"
#!/usr/bin/env -S prepoly --

import package_manager.exec.main

main()
PPM
chmod +x "$ppm_path"

#
# libraries
#

./libraries/build.sh release

for path in $(find libraries -type f | grep -e '\.pp$' -e '\.so$'); do
    mkdir -p "$tmp/$(dirname "$path")"
    cp "$path" "$tmp/$path"
done

#
# make tarball
#

cd "$tmp"
find bin libraries -type f | xargs tar czf "$cwd/prepoly-$(rustc --print=host-tuple).tar.gz"

cd "$cwd"
rm -rf "$tmp"
