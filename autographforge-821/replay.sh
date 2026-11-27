#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
cd -- "${MATHLIB_DIR:?Set MATHLIB_DIR to a prepared Mathlib v4.19.0 checkout}"
[[ "$(git rev-parse HEAD)" == c44e0c8ee63ca166450922a373c7409c5d26b00b ]]
version=$(lake env lean --version)
[[ "$version" == *"version 4.19.0,"* ]]
echo "$version"
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
compiler=$(lake env which lean)
search=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$obj:$search"
if [[ ! -f .lake/build/lib/lean/Mathlib/Data/Multiset/Sort.olean ]]; then
  cp -as "$PWD/.lake/build/lib/lean/Mathlib" "$obj/Mathlib"
  "$compiler" -DwarningAsError=true --root="$PWD" -o "$obj/Mathlib/Data/Multiset/Sort.olean" Mathlib/Data/Multiset/Sort.lean
fi
"$compiler" --root="$src/../autographforge-370" -DwarningAsError=true -o "$obj/OuterForest.olean" "$src/../autographforge-370/OuterForest.lean"
"$compiler" --root="$src" -DwarningAsError=true "$src/ForestSlater.lean" | tee "$obj/check"
for theorem in forest_path_bound tree_path_bound row821_connected row821_graphcalc two_isolates_slater row821_infinity_counterexample; do
  grep -Fxq "'ForestSlater.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/check"
done
