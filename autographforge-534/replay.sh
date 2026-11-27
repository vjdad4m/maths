#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/compile.sh" Proof137 CographJoin IndependentBasis Restrained Row534 Equality Stars | tee "$obj/axioms.log"
for theorem in cone_formula independent_universal nonuniversal_cograph join_criterion criterion row534 dominating_pair_iff join_equality star_exact singleton_join_discrepancy; do
  grep -Fxq "'Restrained534.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
if grep -Eq 'sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler' "$obj/axioms.log"; then exit 1; fi
