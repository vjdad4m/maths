#!/usr/bin/env bash
# Run from a shell where Lean 4.19.0 and the pinned mathlib build are available
# (e.g. lake env bash /path/to/replay.sh).
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
lean --version
cd "$here"
for m in RankBound Conventional LeafBound LeafStructure Large SmallNumerics SmallChunk{0..8} Small Combine Two Assembly TwinConnected TwinRandic PrincipalRank RankTwo Final Complete; do
  lean -j1 -s 65536 -DwarningAsError=true -o "$build/$m.olean" "$m.lean"
done
