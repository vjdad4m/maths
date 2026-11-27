#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
obj="$(mktemp -d)"
trap 'rm -rf "$obj"' EXIT
export LEAN_PATH="$obj${LEAN_PATH:+:$LEAN_PATH}"
lean --version
for pkg in "$here/../graffiti-180-chord-criteria" "$here/../graffiti-180-core-exchanges" "$here/../graffiti-180-controlled-pair-exchanges" "$here"; do
  while IFS= read -r n; do
    lean -j1 -s 65536 -DwarningAsError=true --root="$pkg/src" -o "$obj/$n.olean" "$pkg/src/$n.lean"
  done < "$pkg/modules.txt"
done
