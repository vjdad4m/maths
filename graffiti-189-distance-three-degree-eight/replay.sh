#!/usr/bin/env bash
set -euo pipefail
p=$(cd "$(dirname "$0")" && pwd)
lean --version | grep -q '4.19.0.*6caaee842e94'
(cd "$p" && sha256sum -c SOURCE-SHA256.txt)
o=$(mktemp -d)
export LEAN_PATH="$o:${LEAN_PATH:-}"
while IFS= read -r m; do
  lean --root="$p/src" -j1 -DElab.async=false -DwarningAsError=true -o "$o/$m.olean" "$p/src/$m.lean"
done <"$p/modules.txt"
