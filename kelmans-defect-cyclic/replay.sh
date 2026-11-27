#!/usr/bin/env bash
# Run with: lake env bash /path/to/maths/kelmans-defect-cyclic/replay.sh
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
base="${1:-$here/../kelmans-defect}"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
lean --version
for package in "$base" "$here"; do
  while IFS= read -r module; do
    lean -j1 -DwarningAsError=true --root="$package/src" \
      -o "$build/$module.olean" "$package/src/$module.lean"
  done < "$package/modules.txt"
done
