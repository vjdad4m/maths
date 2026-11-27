#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
obj="$(mktemp -d)"
trap 'rm -rf "$obj"' EXIT
export LEAN_PATH="$obj${LEAN_PATH:+:$LEAN_PATH}"
build() {
  local dir="$here/../$1" module="$2"
  lean -j1 -DElab.async=false -DwarningAsError=true --root="$dir" \
    -o "$obj/$module.olean" "$dir/$module.lean"
}
build autographforge-720 ClawRainbow
build autographforge-242 Proof242
