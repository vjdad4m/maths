#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
cd -- "${MATHLIB_DIR:?Set MATHLIB_DIR to the prepared Mathlib 4.19.0 source checkout}"
[[ "$(git rev-parse HEAD)" == c44e0c8ee63ca166450922a373c7409c5d26b00b ]]
version=$(lake env lean --version)
[[ "$version" == *"version 4.19.0,"* ]]
echo "$version"
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
if [[ ! -e .lake/build/lib/lean/Mathlib/Combinatorics/Enumerative/DoubleCounting.olean ]]; then
  lake build Mathlib.Combinatorics.Enumerative.DoubleCounting >/dev/null
fi
compiler=$(lake env which lean)
search=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$obj:$search"
"$compiler" --root="$src" -DwarningAsError=true "$src/ClawRainbow.lean" | tee "$obj/result"
for theorem in strict_count row720_of_edge row720 sharp_K2; do
  grep -Fxq "'ClawRainbow720.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/result"
done
