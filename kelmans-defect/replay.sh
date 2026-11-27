#!/usr/bin/env bash
# Run with: lake env bash /path/to/maths/kelmans-defect/replay.sh
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
lean --version
while IFS= read -r module; do
  lean -j1 -DwarningAsError=true --root="$here/src" \
    -o "$build/$module.olean" "$here/src/$module.lean"
done < "$here/modules.txt"
