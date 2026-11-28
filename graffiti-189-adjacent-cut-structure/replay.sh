#!/usr/bin/env bash
set -euo pipefail
# Requires Lean 4.19 and LEAN_PATH containing compatible Mathlib and
# CrossSaturation189.olean (including its transitive imports).
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
export LEAN_PATH="$tmp${LEAN_PATH:+:$LEAN_PATH}"
for mod in AdjacentCutFiveBound189 AdjacentCutFiveActual189 AdjacentCutFiveComponents189 AdjacentCutFiveAsymmetry189; do
  lean --root="$PWD" -j1 -DElab.async=false -DwarningAsError=true -o "$tmp/$mod.olean" "$mod.lean"
done
