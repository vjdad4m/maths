#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" MatchingBasis Row1078 Bound FamilyGraph Row574 Compact | tee "$obj/axioms.log"
for theorem in TriangleMatching1078.minDegree_le_lineDomination EulerDom574.upper EulerDom574.eulerian_upper EulerDom574.matching_values EulerDom574.family EulerDom574.row574_false EulerDom574.Compact.witness; do
  grep -Fxq "'$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
