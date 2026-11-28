#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
bash "$src/../autographforge-595/compile.sh" Matching Blocks Packing Row595
bash "$src/../autographforge-1160/compile.sh" Criterion Witness
cd "${MATHLIB_DIR:?Set MATHLIB_DIR}"
search="$obj:$PWD/.lake/build/lib/lean"
for dep in "$PWD"/.lake/packages/*/.lake/build/lib/lean; do search="$search:$dep"; done
export LEAN_PATH="$search"
lean -j1 --root="$src" -DwarningAsError=true "$src/Transfer.lean" | tee "$obj/axioms.log"
for thm in counterexample row837 row838 row839 row840 row841 row843 row844 row845 row846 row847 row832 row848 row849 row850 row851 row1161 row1162; do
  grep -Fxq "'CubicBridges1160.$thm' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
