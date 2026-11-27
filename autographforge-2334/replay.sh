#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
mathlib=${MATHLIB_DIR:?Set MATHLIB_DIR to a prepared Mathlib 4.19.0 checkout}
cd -- "$mathlib"
[[ "$(git rev-parse HEAD)" == c44e0c8ee63ca166450922a373c7409c5d26b00b ]]
version=$(lake env lean --version)
[[ "$version" == *"version 4.19.0,"* ]]
echo "$version"
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
search=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$obj:$search"
compiler=$(lake env which lean)
"$compiler" --root="$src/../autographforge-370" -DwarningAsError=true -o "$obj/OuterForest.olean" "$src/../autographforge-370/OuterForest.lean"
"$compiler" --root="$src" -DwarningAsError=true "$src/BranchedTree.lean" | tee "$obj/result"
for name in acyclic_of_unique_lower tri_upper counterexample; do
  grep -Fxq "'AutoGraphForge2334.$name' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/result"
done
