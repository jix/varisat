#!/bin/bash
set -eu

PACKAGES=(
    varisat
    varisat-cli
    varisat-macros
)

VER=$(sed -ne 's/^version = "\(.*\)".*/\1/;T;p;q' varisat/Cargo.toml)

for PACKAGE in "${PACKAGES[@]}"; do
    PKG_VER=$(sed -ne 's/^version = "\(.*\)".*/\1/;T;p;q' varisat/Cargo.toml)

    if [[ $PKG_VER != $VER ]]; then
        echo "$PACKAGE has version $PKG_VER != $VER" >&2
        exit 1
    fi
done

FILES=(
    varisat/src/lib.rs
    README.md
    varisat/README.md
)

for FILE in "${FILES[@]}"; do
    if ! fgrep -q https://jix.github.io/varisat/manual/$VER/ $FILE; then
        echo "Manual link in $FILE is not up to date" >&2
        exit 1
    fi
done

FILES=(
    README.md
    varisat/README.md
    manual/src/lib/README.md
    manual/src/README.md
)

for FILE in "${FILES[@]}"; do
    if ! fgrep -q https://docs.rs/varisat/$VER/varisat/ $FILE; then
        echo "API docs link in $FILE is not up to date" >&2
        exit 1
    fi
done

if ! git tag -l v$VER | grep -q .; then
    git tag -a v$VER -m "Release of version $VER"
fi

git describe --tags --match='v[0-9]*' --dirty='-d' '--always' | sed 's/^v//'
