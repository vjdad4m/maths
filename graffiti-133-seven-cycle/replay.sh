#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
lean --version
for package in "$here/../graffiti-133-density" "$here/../graffiti-133-floor-three" "$here/../graffiti-133-real-three" "$here/../graffiti-133-five-free" "$here"; do
  while IFS= read -r module; do
    lean -j1 -DwarningAsError=true --root="$package/src" \
      -o "$build/$module.olean" "$package/src/$module.lean"
  done < "$package/modules.txt"
done
