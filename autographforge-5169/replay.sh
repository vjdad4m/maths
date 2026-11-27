#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" MatchingBasis Row1078 Proof137 Patterns Local Cover Obstructions Patch Packing Bound Reused Chain Row5169 ClawMatching Sharp Unrestricted | tee "$obj/axioms.log"
for theorem in matching_exact cover_exact five_per_edge minimal_order duplicate family row5169_false subcubic near_perfect cover_from_matching connected_cover connected_minimal_order smallest_connected unrestricted_minimal_order smallest_unrestricted; do
  grep -Fxq "'Chain5169.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
