#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
export LEAN_PATH="$tmp${LEAN_PATH:+:$LEAN_PATH}"
while IFS= read -r mod; do
  lean --root="$PWD" -j1 -DElab.async=false -DwarningAsError=true -o "$tmp/$mod.olean" "$mod.lean"
done < order.txt
