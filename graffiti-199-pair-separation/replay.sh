#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
obj="$(mktemp -d)"
trap 'rm -rf "$obj"' EXIT
export LEAN_PATH="$obj${LEAN_PATH:+:$LEAN_PATH}"
lean --version
for pkg in "$here/../graffiti-199-small-cut-configurations" "$here/../graffiti-199-overlap-adapters" "$here/../graffiti-199-four-block-integration" "$here/../graffiti-199-four-loss-tree-budget" "$here/../graffiti-199-separated-four-blocks" "$here"; do
  while IFS= read -r n; do
    lean -j1 -s 65536 -DwarningAsError=true --root="$pkg/src" -o "$obj/$n.olean" "$pkg/src/$n.lean"
  done < "$pkg/modules.txt"
done
