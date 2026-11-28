#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SOURCES.sha256
obj="$(mktemp -d)"
trap 'rm -rf "$obj"' EXIT
export LEAN_PATH="$obj${LEAN_PATH:+:$LEAN_PATH}"
while read -r mod; do
 lean --root="$PWD/src" -j1 -s65536 -DElab.async=false -DwarningAsError=true -o "$obj/$mod.olean" "src/$mod.lean"
done < order.txt
