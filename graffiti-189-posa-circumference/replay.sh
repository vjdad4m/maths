#!/usr/bin/env bash
set -euo pipefail
# Lean and Mathlib 4.19, prior #189 sources' objects on LEAN_PATH.
root=$(cd "$(dirname "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf "$obj"' EXIT
export LEAN_PATH="$obj:${LEAN_PATH:-}"
for m in PosaGreedy189 PosaCrossing189 PosaBridges189 PosaCycleExtend189 PosaSpine189 \
  PosaTracks189 PosaOrderedPair189 PosaBridgeAdapter189 PosaRouteCut189 PosaSpliceCommon189 \
  PosaSameSplice189 PosaCrossSplice189 PosaMaxCover189 PosaCycleCover189 PosaCrossCycle189 \
  PosaEndpointCycle189 PosaOneLow189; do
  echo "== $m =="
  lean -j1 -DElab.async=false -DwarningAsError=true --root="$root" -o "$obj/$m.olean" "$root/$m.lean"
done
