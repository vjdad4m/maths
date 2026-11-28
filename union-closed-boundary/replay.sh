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
  for f in Boundary ThirdDegree FourthDegree FifthDegree CycleObstruction; do
    lean -j1 -DElab.async=false --root="$src" -DwarningAsError=true -o "$obj/$f.olean" "$src/$f.lean"
  done
} | tee "$obj/axioms.log"
for thm in weighted_coefficients weighted_coefficients_third phan_third weighted_fourth phan_fourth fifth_mass_of_singletons fifth_of_symmetric_cores phan_fifth_of_symmetric_complements fifth_of_large_core fifth_of_asymmetric_max_core c6_intersection_closed c6_no_common_coordinate; do
  grep -Fxq "'UnionClosedBoundary.$thm' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
