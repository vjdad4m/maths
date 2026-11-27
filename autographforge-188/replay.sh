#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" Proof137 CographJoin ForcingBasis PowerBasis Components Row188 TwinFort Sharp | tee "$obj/axioms.log"
for theorem in active_in_component small_shore convert_components comparison row188 Sharp.sharp; do
  grep -Fxq "'CographForcing188.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
