#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" MatchingBasis Row1078 Proof137 Patterns Local Cover HallRainbow Boundary Deficiency Row1553 | tee "$obj/axioms.log"
for theorem in sharp_row deficiency cover_of_k_dominating rainbow_edge_bound row1553 clique_cover_le_edge_cover biclique_excess sharp_family; do
  grep -Fxq "'RainbowCover1553.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
