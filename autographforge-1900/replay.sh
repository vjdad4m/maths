#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" OuterForest Criterion HallRainbow Boundary DegreeTwo Row1900 Sharp | tee "$obj/axioms.log"
for theorem in star_complement max_degree_bound triangle_cover row1900 equality_criterion Sharp.biclique_sharp Sharp.square; do
    grep -Fxq "'OuterStar1900.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
