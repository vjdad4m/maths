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
"$compiler" -j1 --root="$src" -DwarningAsError=true "$src/QuasiLineRoman.lean" | tee "$obj/result"
for theorem in cover_eq_chromatic quasiline_bound quasiline_of_degree_four row621 degree_five_boundary; do
  grep -Fxq "'QuasiLineRoman621.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/result"
done
