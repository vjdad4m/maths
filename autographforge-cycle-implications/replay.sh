#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
obj="$(mktemp -d)"
trap 'rm -rf "$obj"' EXIT
CYCLE_BUILD="$obj" bash "$here/../autographforge-1130/build.sh" Sharpness TraceableBurn BurnBridge CycleCore CycleDomination
cd "${MATHLIB_DIR:?Set MATHLIB_DIR}"
export LEAN_PATH="$obj:$(lake env printenv LEAN_PATH)"
lean -j1 -DwarningAsError=true "$here/CycleImplications.lean"
