#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" HallRainbow Family Drawing SharpBound Row464 | tee "$obj/axioms.log"
for theorem in planar cover_exact rainbow_exact sharp_value family unbounded row464_false sharp_bound cover_of_deficit rainbow_cover_of_crossEuler; do
  grep -Fxq "'PlanarRainbow464.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
