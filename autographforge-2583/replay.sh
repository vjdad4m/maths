#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
base="$here/../autographforge-1130"
obj="$(mktemp -d)"
trap 'rm -rf "$obj"' EXIT
export CYCLE_BUILD="$obj"
bash "$base/build.sh" Sharpness TraceableBurn BurnBridge CycleCore CycleDomination CyclePlane
cd "${MATHLIB_DIR:?Set MATHLIB_DIR to a prepared Mathlib 4.19.0 checkout}"
compiler="$(lake env which lean)"
search="$(lake env printenv LEAN_PATH)"
export LEAN_PATH="$obj:$search"
"$compiler" -j1 -DElab.async=false -DwarningAsError=true --root="$here" "$here/CycleRow2583.lean" | tee "$obj/row.log"
grep -Fxq "'CycleBatch.row2583' depends on axioms: [propext, Classical.choice, Quot.sound]" "$obj/row.log"
