#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
cd -- "${MATHLIB_DIR:?Set MATHLIB_DIR to the prepared Mathlib 4.19.0 source checkout}"
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
"$compiler" --root="$src" -DwarningAsError=true "$src/SquaredPath.lean" | tee "$obj/result"
for name in connected k4_free claw_free slater_exact diameter_exact row2039_connected_false row2039_false; do
  axioms="[propext, Classical.choice, Quot.sound]"
  if [[ "$name" == claw_free ]]; then axioms="[propext]"; fi
  grep -Fxq "'SquaredPath2039.$name' depends on axioms: $axioms" "$obj/result"
done
