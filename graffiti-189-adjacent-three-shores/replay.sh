#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
export LEAN_PATH="$tmp${LEAN_PATH:+:$LEAN_PATH}"
for m in Bound Actual Components Asymmetry ThreeSingleton Minimal Metric SingletonDepth SingletonGeometry ThreeSingletonClose ThreeNonSingleton ThreeFourCommon ThreeShape ThreeTwins Profiles; do
  mod="AdjacentCutFive${m}189"
  lean --root="$PWD" -j1 -DElab.async=false -DwarningAsError=true -o "$tmp/$mod.olean" "$mod.lean"
done
