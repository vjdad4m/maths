#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
for file in Core Nodal Perron MainLarge Small CliqueBound; do
  LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}" lean -j1 -DElab.async=false -DwarningAsError=true -o "$build/$file.olean" "$file.lean"
done
