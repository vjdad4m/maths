#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" MatchingBasis Row1078 Bound Theta Roman ThetaDrawing Row659 | tee "$obj/axioms.log"
for theorem in packing_lower roman_exact planar family unbounded row659_false; do
  grep -Fxq "'Theta659.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
