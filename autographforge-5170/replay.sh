#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
base=(MatchingBasis Row1078 Proof137 Patterns Local Cover HallRainbow Deficiency)
regular=(Obstructions Regular Spread)
family=(Boundary Row1553 Factor Twin Family)
first=(degree_error almost_regular regular_bound row5174 degree_spread_sharp)
second=(triangle_free_cover family_cover sharp_affine row5170_counterexamples row5170_false)
case "${1:-5170}" in
  5174) modules=("${regular[@]}"); theorems=("${first[@]}") ;;
  5170) modules=("${family[@]}"); theorems=("${second[@]}") ;;
  all) modules=("${regular[@]}" "${family[@]}"); theorems=("${first[@]}" "${second[@]}") ;;
  *) echo 'usage: bash replay.sh [5174|5170|all]' >&2; exit 2 ;;
esac
bash "$src/compile.sh" "${base[@]}" "${modules[@]}" | tee "$obj/axioms.log"
for theorem in "${theorems[@]}"; do
  grep -Fxq "'RegularCover5174.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
