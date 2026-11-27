#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" MatchingBasis Row1078 Bound FamilyGraph Row574 Row583 Sharp Boundary | tee "$obj/axioms.log"
for theorem in of_double_cover of_edge_dominating slater_le_lineDomination eulerian row583 sharp triangle path_four; do
  grep -Fxq "'SlaterEdges583.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
