#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
cd "${MATHLIB_DIR:?Set MATHLIB_DIR to a built Mathlib checkout}"
[[ $(git rev-parse HEAD) == c44e0c8ee63ca166450922a373c7409c5d26b00b ]]
[[ $(lean --version) == *"version 4.19.0,"* ]]
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
search="$obj:$PWD/.lake/build/lib/lean"
for dep in "$PWD"/.lake/packages/*/.lake/build/lib/lean; do search="$search:$dep"; done
export LEAN_PATH="$search"
{
  for f in Akbari Conjecture9; do
    lean -j1 -DElab.async=false --root="$src" -DwarningAsError=true -o "$obj/$f.olean" "$src/$f.lean"
  done
} | tee "$obj/axioms.log"
for thm in edge_count_le_two_randic_sq matching_sq_le_edges_times_randic matching_number_cube_bound explicit_constant conjecture9; do
  grep -Fxq "'AkbariRandic.$thm' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
