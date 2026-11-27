#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" MatchingBasis Row1078 | tee "$obj/axioms.log"
for theorem in degree_le_of_dominating minDegree_le_lineDomination lineDomination_le_matching row1078 sharp; do
  grep -Fxq "'TriangleMatching1078.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
