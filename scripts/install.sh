#!/bin/bash

if [ -z "$PREPOLY_VERSION" ]; then
    # release version
    PREPOLY_VERSION="0.1.0"
fi
PREPOLY_REPO_BASE_URL="https://github.com/cordx56/prepoly"

# print host-tuple
print_host_tuple() {
    if [ -z "$TOOLCHAIN_OS" ]; then
        # Get OS
        case "$(uname -s)" in
            Linux)
                TOOLCHAIN_OS="unknown-linux-gnu"
                ;;
            Darwin)
                TOOLCHAIN_OS="apple-darwin"
                ;;
            CYGWIN*|MINGW32*|MSYS*|MINGW*)
                TOOLCHAIN_OS="pc-windows-msvc"
                ;;
            *)
                echo "Unsupported OS: $(uname -s)" >&2
                exit 1
                ;;
        esac
    fi

    if [ -z "$TOOLCHAIN_ARCH" ]; then
        # Get architecture
        case "$(uname -m)" in
            arm64|aarch64)
                TOOLCHAIN_ARCH="aarch64"
                ;;
            x86_64|amd64)
                TOOLCHAIN_ARCH="x86_64"
                ;;
            *)
                echo "Unsupported architecture: $(uname -m)" >&2
                exit 1
                ;;
        esac
    fi

    echo "$TOOLCHAIN_ARCH-$TOOLCHAIN_OS"
}

HOST_TUPLE="$(print_host_tuple)"

#
# main
#
dest="$HOME/.prepoly"
mkdir -p "$dest"
tar_file="prepoly-$HOST_TUPLE.tar.gz"
if [ "$PREPOLY_VERSION" = "latest" ]; then
    url="$PREPOLY_REPO_BASE_URL/releases/latest/download/$tar_file"
else
    url="$PREPOLY_REPO_BASE_URL/releases/download/$PREPOLY_VERSION/$tar_file"
fi
curl -L "$url" | tar -xz -C "$dest"

echo 'Add $HOME/.prepoly/bin to your PATH to complete the installation.'
