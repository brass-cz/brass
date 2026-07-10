#!/bin/bash -e
#
# Build each library's native plugin and install it beside its Prepoly module,
# under the name that module imports (`process/process.so`). Cargo names a
# cdylib `libprocess.so`; the loader accepts either, but the plain name is what
# the module refers to.
#
# Usage: libraries/build.sh [--release]

cd "$(dirname "$0")/.."

profile_dir=debug
cargo_args=()
if [[ "${1:-}" == "--release" ]]; then
    profile_dir=release
    cargo_args+=(--release)
fi

case "$(uname -s)" in
Darwin) suffix=dylib ;;
MINGW* | MSYS* | CYGWIN*) suffix=dll ;;
*) suffix=so ;;
esac

# package name -> library name (the cdylib's `[lib] name`, and the module name)
libraries=(prepoly_lib_process:process)

for entry in "${libraries[@]}"; do
    package="${entry%%:*}"
    lib="${entry##*:}"
    cargo build -p "$package" "${cargo_args[@]}"

    built="target/$profile_dir/lib$lib.$suffix"
    [[ "$suffix" == dll ]] && built="target/$profile_dir/$lib.$suffix"
    dest="libraries/$lib/$lib.$suffix"

    cp "$built" "$dest"
    echo "installed $dest"
done
