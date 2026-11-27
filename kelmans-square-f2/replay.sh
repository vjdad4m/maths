#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
lean --version
old="$here/../kelmans-twin-obstruction/src"
lean -j1 -DwarningAsError=true --root="$old" -o "$build/TwinObstruction.olean" "$old/TwinObstruction.lean"
for m in SquareCapGeometry SquareCapFactor SquareCapArbitrary; do
  lean -j1 -DwarningAsError=true --root="$here/src" -o "$build/$m.olean" "$here/src/$m.lean"
done
