#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" Criterion Witness | tee "$obj/axioms.log"
for theorem in regular_annihilation regular_triangleFree_criterion connected cover_exact annihilation_exact no_perfect_matching row1160_false; do
  grep -Fxq "'CubicBridges1160.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
