#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out:${LEAN_PATH:-}"
for m in SixCentreParity189 SixCentreCount189 SixCentreGraph189 OtherCentres189 AdamEdgeIdentity189 AdamNearEdge189 AdamEdgeTight189 AdamEdgeTPartition189 AdamEdgeTEconomy189 AdamEdgeLemmaT189; do
  echo "== $m =="
  lean -j1 -DElab.async=false -DwarningAsError=true --root="$src" -o "$out/$m.olean" "$src/$m.lean"
  echo "PASS $m"
done
if [[ ${1:-} == --diameter ]]; then
  lean -j1 -DElab.async=false -DwarningAsError=true --root="$src" "$src/EvenDiameterTwoConnected189.lean"
  echo 'PASS EvenDiameterTwoConnected189'
fi
