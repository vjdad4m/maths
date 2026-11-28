#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export OBJDIR="$obj"
echo "Replay build: $obj" >&2
bash "$src/../autographforge-595/compile.sh" Matching Blocks Packing Row595
bash "$src/../autographforge-1160/compile.sh" Criterion Witness
cd "${MATHLIB_DIR:?Set MATHLIB_DIR to the prepared Mathlib checkout}"
search="$obj:$PWD/.lake/build/lib/lean"
for dep in "$PWD"/.lake/packages/*/.lake/build/lib/lean; do search="$search:$dep"; done
export LEAN_PATH="$search"
prior="$src/../autographforge-cubic-odd-blocks"
lean -j1 --root="$prior" -DwarningAsError=true -o "$obj/Transfer.olean" "$prior/Transfer.lean"
lean -j1 --root="$src" -DwarningAsError=true "$src/OddImplications.lean" | tee "$obj/axioms.log"
for thm in row3232_false row4862_false; do
  grep -Fxq "'CubicBridges1160.$thm' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
