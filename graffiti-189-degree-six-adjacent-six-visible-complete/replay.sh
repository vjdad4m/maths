#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
lean_args=(-j1 -s65536 -DElab.async=false -DwarningAsError=true "--root=$here")
obj="${Q2_OBJ:-$here/obj}"
mkdir -p "$obj"
export LEAN_PATH="$obj${LEAN_PATH:+:$LEAN_PATH}"
cd "$here"
while IFS= read -r m; do
  echo "== $m =="
  "${LEAN_BIN:-lean}" "${lean_args[@]}" -o "$obj/$m.olean" "$here/$m.lean"
  echo "PASS $m"
done < LEAN-MODULES.txt
