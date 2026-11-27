#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" MatchingBasis Row1078 Proof137 Patterns Local Cover Obstructions | tee "$obj/axioms.log"
for theorem in coverable_iff cover_from_domination bound row1125 claw_values bull_values hereditary_iff row_sharp; do
  grep -Fxq "'BullCover1125.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
