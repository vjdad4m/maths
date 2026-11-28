#!/usr/bin/env bash
# Run inside a Lean 4.19.0 environment with this version of Mathlib on LEAN_PATH.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
obj="$(mktemp -d)"
export LEAN_PATH="$obj${LEAN_PATH:+:$LEAN_PATH}"
for m in Base189 ThreeCut189 Cut189 Components189 Path189 Summary189; do
  echo "Checking $m"
  "${LEAN_BIN:-lean}" -j1 -s65536 -DElab.async=false -DwarningAsError=true "--root=$here" -o "$obj/$m.olean" "$here/$m.lean"
done
echo "All six modules passed."
