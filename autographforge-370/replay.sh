#!/usr/bin/env bash
set -euo pipefail
here=$(cd -- "$(dirname -- "$0")" && pwd)
mathlib=${MATHLIB_DIR:-"$here/.deps/mathlib4"}
if [[ -d "$here/.deps/lean-4.19.0-linux/bin" && -z "${MATHLIB_DIR:-}" ]]; then
  export PATH="$here/.deps/lean-4.19.0-linux/bin:$PATH"
fi
cd -- "$mathlib"
expected=c44e0c8ee63ca166450922a373c7409c5d26b00b
[[ "$(git rev-parse HEAD)" == "$expected" ]] || { echo "Expected Mathlib $expected" >&2; exit 1; }
version=$(lake env lean --version)
[[ "$version" == *"version 4.19.0,"* ]] || { echo "$version" >&2; exit 1; }
echo "$version"
result=$(lake env lean -DwarningAsError=true "$here/OuterForest.lean") || { echo "$result"; exit 1; }
echo "$result"
for theorem in forest_of_bipartite_chordal forest_indep_le_outer_card outerNumber_defined_iff row370; do
  grep -Fxq "'AutoGraphForge370.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" <<< "$result"
done
