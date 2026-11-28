#!/bin/bash
set -euo pipefail
root=$(cd "$(dirname "$0")" && pwd)
cd "$root"
sha256sum -c SOURCES.sha256
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out${LEAN_PATH:+:$LEAN_PATH}"
for m in MarkedWingSat189 MarkedWing60Cert189 MarkedWing62Cert189 MarkedWing70Cert189 MarkedWing72Cert189 MarkedWing80Cert189 MarkedWing82Cert189 MarkedWingPath189 DenseOwnerRoute189 FiveCheapBudget189 FiveSharedCharges189 FiveEdgeBudget189 FiveEdgeLayout189 FiveLongerWord189 FiveMidBudget189 FiveMidSplice189 FivePinLayout189 SixFourOrderTwentyThree189; do
  lean -j1 -s32768 -DElab.async=false -DwarningAsError=true --root="$root" -o "$out/$m.olean" "$root/$m.lean"
done
