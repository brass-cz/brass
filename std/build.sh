#!/bin/bash -e
#
# Usage: std/build.sh [profile]

cd "$(dirname "$0")/.."

profile="${1:-"release"}"
target_profile="$profile"
[[ "$profile" == dev ]] && target_profile=debug

case "$(uname -s)" in
Darwin) suffix=dylib ;;
MINGW* | MSYS* | CYGWIN*) suffix=dll ;;
*) suffix=so ;;
esac

while IFS= read -r manifest; do
    dirpath="$(dirname "$manifest")"
    libname="$(basename "$dirpath")"
    pkgname="brass_lib_$libname"
    cargo build -p "$pkgname" --profile="$profile"

    built="target/$target_profile/lib$libname.$suffix"
    [[ "$suffix" == dll ]] && built="target/$target_profile/$libname.$suffix"

    basedir="$(dirname "$dirpath")"
    mkdir -p "$basedir"
    cp "$built" "$basedir/lib$libname.$suffix"
    echo "lib$libname built"
done < <(find std -type f -name Cargo.toml)
