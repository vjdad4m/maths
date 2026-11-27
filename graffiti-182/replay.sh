#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
base="$(dirname "$here")/graffiti-183"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
lean --version
compile() {
  local dir="$1" module="$2"
  lean -j1 -s 65536 -DwarningAsError=true --root="$dir" -o "$build/$module.olean" "$dir/$module.lean"
}
while IFS= read -r module; do
  compile "$base/src" "$module"
done < "$base/modules.txt"
for module in Reduction182 Bridge182 Proof182; do
  compile "$here" "$module"
done
