#!/bin/bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
(cd "$here" && sha256sum -c sources.sha256)
obj=$(mktemp -d)
trap 'rm -rf "$obj"' EXIT
export LEAN_PATH="$obj:$LEAN_PATH"
while IFS= read -r m; do
  lean --root="$here/src" -j1 -s32768 -DElab.async=false -DwarningAsError=true -o "$obj/$m.olean" "$here/src/$m.lean"
done < "$here/modules.txt"
