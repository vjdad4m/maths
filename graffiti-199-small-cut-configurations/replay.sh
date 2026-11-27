#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
export LEAN_PATH="$tmp${LEAN_PATH:+:$LEAN_PATH}"
lean --version
python3 "$here/generate_depleted_paths.py" > "$tmp/DepletedPaths.lean"
cmp "$tmp/DepletedPaths.lean" "$here/src/DepletedPaths.lean"
rm "$tmp/DepletedPaths.lean"
while IFS= read -r module; do
  lean --root="$here/src" -j1 -s 65536 -DwarningAsError=true \
    -o "$tmp/$module.olean" "$here/src/$module.lean"
done < "$here/modules.txt"
