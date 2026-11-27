#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
cd -- "${MATHLIB_DIR:?Set MATHLIB_DIR to the prepared Mathlib v4.19.0 checkout}"
[[ $(git rev-parse HEAD) == c44e0c8ee63ca166450922a373c7409c5d26b00b ]]
lean=$(lake env which lean)
search=$(lake env printenv LEAN_PATH)
version=$("$lean" --version)
[[ "$version" == *"version 4.19.0,"* ]]
echo "$version"
obj=$(mktemp -d)
trap 'rm -rf -- "$obj"' EXIT
export LEAN_PATH="$obj:$search"
for module in HallRainbow Boundary; do
  "$lean" -j1 -DElab.async=false --root="$src" -DwarningAsError=true -o "$obj/$module.olean" "$src/$module.lean" | tee -a "$obj/axioms.log"
done
for theorem in match_outside cover_of_matching cover_of_rainbow rainbow_bound row1121 biclique_degrees biclique_boundary; do
  grep -Fxq "'HallRainbow1121.$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/axioms.log"
done
