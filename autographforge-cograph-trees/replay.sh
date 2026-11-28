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
  local pkg="$1"
  shift
  for module in "$@"; do
    lean -j1 --root="$pkg" -DwarningAsError=true -o "$obj/$module.olean" "$pkg/$module.lean"
  done
}
build "$base/autographforge-534" Proof137 CographJoin
build "$base/autographforge-370" OuterForest
build "$base/graffiti-324" Proof324
build "$base/autographforge-1160" Criterion
build "$src" StarStructure StarNumbers Rows | tee "$obj/axioms.log"
for thm in star_of_tree_cograph outer star_residue star_annihilation star_edge_cover cograph_tree_profile \
  row1173 row1178 row1181 row1212 row1215 row1227 row1229 row1257 row1272 row1314 row1316 \
  row1415 row1416 row1638 row1640 row1643 row1644; do
  grep -Fxq "'CographTree.$thm' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
