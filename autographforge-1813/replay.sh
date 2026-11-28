#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
obj="$(mktemp -d)"
trap 'rm -rf "$obj"' EXIT
OBJDIR="$obj" bash "$here/../autographforge-595/compile.sh" Matching Blocks Packing Row595
cd "${MATHLIB_DIR:?Set MATHLIB_DIR}"
export LEAN_PATH="$obj:$(lake env printenv LEAN_PATH)"
lean -j1 -DwarningAsError=true "$here/CliqueHarmonic.lean"
