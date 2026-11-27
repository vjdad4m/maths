#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" MatchingBasis Row1078 HallRainbow Factor Twin Archive DegreeBound Row1957 | tee "$obj/axioms.log"
for theorem in cover_of_vertex_cover catalogue_factor_two bipartite_degree_bound fixed_degree_equality family sharp_affine row1957_false Archive.edge_exact Archive.cover_exact Archive.released_witness; do
  grep -Fxq "'RegularCliques1957.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
