#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" MatchingBasis Row1078 HallRainbow Bound Packing Graph Independent Row791 | tee "$obj/axioms.log"
for theorem in independent_rigid match_exact weight_lower rainbow_exact certificate row791_false other_spellings; do
  grep -Fxq "'CubicRainbow791.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
