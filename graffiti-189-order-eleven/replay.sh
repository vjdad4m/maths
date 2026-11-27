#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
lean --version
for package in "$here/../graffiti-189" "$here/../graffiti-189-degree-four" "$here/../graffiti-189-four-vertex-side" "$here/../graffiti-189-distance-three" "$here"; do
  while IFS= read -r module; do
    [[ -s "$build/$module.olean" ]] && continue
    lean -j1 -DwarningAsError=true --root="$package/src" -o "$build/$module.olean" "$package/src/$module.lean"
  done < "$package/modules.txt"
done
