#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" Row711 | tee "$obj/axioms.log"
for theorem in row711 forcing_drop seed_savings packed_seed_savings search_start complete_forcing complete_sharp singleton_boundary triangle_sharp; do
  grep -Fxq "'ForcingDrop711.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
