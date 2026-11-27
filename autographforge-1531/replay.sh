#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" MatchingBasis Row1078 Proof137 Patterns Local Cover Obstructions Patch Packing Row2560 Proof271 ConnectedCore LeavesCore BFS DegreesLeaves DegreeTwoClass IsoCover Bounds Equality Examples | tee "$obj/axioms.log"
for theorem in row1531 count_dominated_edges connected_cover_bound equality_orders equality_iff connected_cover_exact sharp_paths; do
  grep -Fxq "'EdgeCover1531.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
