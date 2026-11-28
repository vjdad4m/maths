#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SOURCES.sha256
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out${LEAN_PATH:+:$LEAN_PATH}"
while read -r x; do
  echo "== $x =="
  lean -j1 -s65536 -DElab.async=false -DwarningAsError=true --root="$PWD" -o "$out/$x.olean" "$PWD/$x.lean"
  echo "PASS $x"
done < MODULES.txt
