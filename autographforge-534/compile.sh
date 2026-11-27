#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
cd "${MATHLIB_DIR:?Set MATHLIB_DIR to the prepared Mathlib v4.19.0 checkout}"
[[ $(git rev-parse HEAD) == c44e0c8ee63ca166450922a373c7409c5d26b00b ]]
obj=${OBJDIR:-$(mktemp -d)}
if [[ -z "${OBJDIR:-}" ]]; then trap 'rm -rf -- "$obj"' EXIT; fi
mkdir -p "$obj"
search="$obj:$PWD/.lake/build/lib/lean"
for dep in "$PWD"/.lake/packages/*/.lake/build/lib/lean; do search="$search:$dep"; done
export LEAN_PATH="$search"
version=$(lean --version)
[[ "$version" == *"version 4.19.0,"* ]]
echo "$version"
for module in "$@"; do
  lean -j1 --root="$src" -DwarningAsError=true -o "$obj/$module.olean" "$src/$module.lean"
done
