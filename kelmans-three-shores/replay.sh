#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
lean --version
for package in "$here/../kelmans-defect" "$here/../kelmans-defect-cyclic" "$here/../kelmans-affine-t2" "$here/../kelmans-handle" "$here/../kelmans-single-cut" "$here/../kelmans-one-handle" "$here/../kelmans-domino-f1" "$here"; do
  while IFS= read -r module; do
    lean -j1 -DwarningAsError=true --root="$package/src" \
      -o "$build/$module.olean" "$package/src/$module.lean"
  done < "$package/modules.txt"
done
