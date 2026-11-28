#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "$0")" && pwd)"
obj="$(mktemp -d)"
trap 'rm -rf "$obj"' EXIT
export LEAN_PATH="$obj${LEAN_PATH:+:$LEAN_PATH}"
for module in BagWalkLift189 SpineWalk189 BagSpineCriterion189 TreeTightSpine189 \
    BagQuotient189 TreeParity189 BagCut189 WeightedTreeSums189 TreeBagCharges189 \
    TreeBagArithmetic189 TreeBagCapacity189 TreeBagTight189 TreeBagTraceability189 \
    SmallTightTreeBag189 AllTightTreeBag189 TreeBagTraceabilityAll189; do
  printf '== %s ==\n' "$module"
  lean -j1 -DElab.async=false -DwarningAsError=true --root="$root" \
    -o "$obj/$module.olean" "$root/$module.lean"
done
