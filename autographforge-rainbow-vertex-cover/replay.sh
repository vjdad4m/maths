#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
cd "${MATHLIB_DIR:?Set MATHLIB_DIR to a prepared Mathlib v4.19.0 checkout}"
[[ $(git rev-parse HEAD) == c44e0c8ee63ca166450922a373c7409c5d26b00b ]]
[[ $(lean --version) == *"version 4.19.0,"* ]]
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
search="$obj:$PWD/.lake/build/lib/lean"
for dep in "$PWD"/.lake/packages/*/.lake/build/lib/lean; do search="$search:$dep"; done
export LEAN_PATH="$search"
prior="$src/../autographforge-1121"
lean -j1 --root="$prior" -DwarningAsError=true -o "$obj/HallRainbow.olean" "$prior/HallRainbow.lean"
lean -j1 --root="$src" -DwarningAsError=true "$src/RainbowVertexCover.lean" | tee "$obj/axioms.log"
for thm in colored_neighbors colored_is_vertex_cover vertex_cover_le_rainbow rows645_671; do
  grep -Fxq "'HallRainbow1121.$thm' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
