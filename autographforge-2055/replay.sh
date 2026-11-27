#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
obj="$(mktemp -d)"
trap 'rm -rf "$obj"' EXIT
export LEAN_PATH="$obj${LEAN_PATH:+:$LEAN_PATH}"
lean --version
run() {
  local dir="$1" m="$2"
  lean -j1 -s 65536 -DwarningAsError=true --root="$dir" -o "$obj/$m.olean" "$dir/$m.lean"
}
for m in Proof271 ConnectedCore LeavesCore BFS DegreesLeaves DegreeTwoClass; do
  run "$here/../graffiti-183/src" "$m"
done
for m in TraceableBurn Sharpness Row2055 P10; do
  run "$here/src" "$m"
done
