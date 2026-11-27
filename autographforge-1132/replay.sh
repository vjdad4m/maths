#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" OuterForest HallRainbow Row1132 Sharp | tee "$obj/axioms.log"
for theorem in cover_cycle_rank numerical_cycle_rank tree_bound row5385 row1132 Sharp.sharp_family; do
    grep -Fxq "'OuterCliques1132.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
