#!/usr/bin/env bash
set -euo pipefail
P="$(cd "$(dirname "$0")" && pwd)"
O="${Q8_BUILD:-$(mktemp -d)}"
mkdir -p "$O"
export LEAN_PATH="$O${LEAN_PATH:+:$LEAN_PATH}"
while IFS= read -r m; do
  [ -n "$m" ] || continue
  "${LEAN:-lean}" --root="$P/src" -j1 -s32768 -DElab.async=false -DwarningAsError=true "$P/src/$m.lean" -o "$O/$m.olean"
done < "$P/modules.txt"
