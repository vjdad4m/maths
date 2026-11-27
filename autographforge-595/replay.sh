#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" Matching Blocks Packing Row595 | tee "$obj/axioms.log"
for theorem in regular_criterion matching_exact family row595_false odd_witness henning_yeo_threshold; do
  grep -Fxq "'RegularHarmonic595.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
