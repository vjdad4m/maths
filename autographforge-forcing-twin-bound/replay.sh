#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
base="$src/.."
cd "${MATHLIB_DIR:?Set MATHLIB_DIR to a prepared Mathlib v4.19.0 checkout}"
[[ $(git rev-parse HEAD) == c44e0c8ee63ca166450922a373c7409c5d26b00b ]]
[[ $(lean --version) == *"version 4.19.0,"* ]]
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
search="$obj:$PWD/.lake/build/lib/lean"
for dep in "$PWD"/.lake/packages/*/.lake/build/lib/lean; do search="$search:$dep"; done
export LEAN_PATH="$search"
build() {
  local pkg="$1" module="$2"
  lean -j1 -DElab.async=false --root="$pkg" -DwarningAsError=true -o "$obj/$module.olean" "$pkg/$module.lean"
}
build "$base/autographforge-star" StarCone
{
  build "$src" TwinForcing
  build "$src" PageBlocks
} | tee "$obj/axioms.log"
for thm in fort_disjoint_iterate twin_seed_quota sum_twin_quota uniform_twin_quota page_forcing_lower page_two_forcing_exact; do
  grep -Fxq "'TwinForcing.$thm' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
