#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" Proof137 CographJoin PowerBasis ChordalBasis Counts Structure Hereditary | tee "$obj/axioms.log"
for thm in universal_of_join exact row105 four_optima four_vertex_test characterization on_induced; do
  grep -Fxq "'Hereditary105.$thm' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
