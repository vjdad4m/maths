#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
obj="$(mktemp -d)"
trap 'rm -rf "$obj"' EXIT
cd "${MATHLIB_DIR:?Set MATHLIB_DIR}"
test "$(git rev-parse HEAD)" = c44e0c8ee63ca166450922a373c7409c5d26b00b
export LEAN_PATH="$obj:$(lake env printenv LEAN_PATH)"
base="$here/../autographforge-star"
lean -j1 --root="$base" -DwarningAsError=true -o "$obj/StarCone.olean" "$base/StarCone.lean"
lean -j1 -DwarningAsError=true "$here/StarImplications.lean"
