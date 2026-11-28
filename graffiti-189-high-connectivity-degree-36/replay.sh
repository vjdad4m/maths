#!/usr/bin/env bash
set -euo pipefail
# Lean and Mathlib 4.19, prior #189 sources' objects on LEAN_PATH.
root=$(cd "$(dirname "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf "$obj"' EXIT
export LEAN_PATH="$obj:${LEAN_PATH:-}"
for m in OneDefectHall189 DefectiveCharge189 DefectiveWideCut189 DefectiveConnectivity189 \
  DefectiveTerminal189 DefectiveFanPorts189 JointLitBudget189 OversizedRoutable189 \
  OversizedShore189 OversizedClosure189; do
  echo "== $m =="
  lean -j1 -DElab.async=false -DwarningAsError=true --root="$root" -o "$obj/$m.olean" "$root/$m.lean"
done
