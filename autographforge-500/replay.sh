#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
obj="$(mktemp -d)"
trap 'rm -rf "$obj"' EXIT
cd "${MATHLIB_DIR:?Set MATHLIB_DIR}"
test "$(git rev-parse HEAD)" = c44e0c8ee63ca166450922a373c7409c5d26b00b
export LEAN_PATH="$obj:$(lake env printenv LEAN_PATH)"
replay() { lean -j1 --root="$1" -DwarningAsError=true -o "$obj/$2.olean" "$1/$2.lean"; }
for m in Proof137 CographJoin IndependentBasis Restrained; do replay "$here/../autographforge-534" "$m"; done
replay "$here/../autographforge-370" OuterForest
lean -j1 -DwarningAsError=true "$here/JoinOuter.lean"
