#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
base="${1:-$here/../graffiti-189}"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
lean --version
for module in SmallSeparator189; do
  lean -j1 -DwarningAsError=true --root="$base/src" \
    -o "$build/$module.olean" "$base/src/$module.lean"
done
while IFS= read -r module; do
  lean -j1 -DwarningAsError=true --root="$here/src" \
    -o "$build/$module.olean" "$here/src/$module.lean"
done < "$here/modules.txt"
