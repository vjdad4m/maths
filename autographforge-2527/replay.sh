#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" MatchingBasis Row1078 Bound Theta ThetaDrawing Independent Crown Row2527 | tee "$obj/axioms.log"
for theorem in star_of_one one_boundary bipartite_one Crown.values family unbounded no_bound row2527_false; do
  grep -Fxq "'ThetaIndependent2527.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
