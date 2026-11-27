#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" MatchingBasis Row1078 Proof137 Patterns Local Cover Obstructions Patch Packing Row2560 | tee "$obj/axioms.log"
for theorem in packing_order packing_zero_iff bull_packing_sharp patch_estimate refined row2560 sharp; do
  grep -Fxq "'Packing2560.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
