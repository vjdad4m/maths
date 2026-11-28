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
build "$base/graffiti-324" Proof324
build "$base/autographforge-book-forts" ChordalBasis
{
  build "$src" Witness676
  build "$src" Chordal676
} | tee "$obj/axioms.log"
for thm in forcing_exact residue_exact connected chordal k4_free counterexample row676_false; do
  grep -Fxq "'AutoGraphForge676.$thm' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
