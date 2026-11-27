#!/usr/bin/env bash
# Run as: lake env bash /path/to/maths/graffiti-186/replay.sh
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(dirname "$here")"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
lean --version
compile() {
  local source="$1" module
  module="$(basename "$source" .lean)"
  lean -DwarningAsError=true --root="$(dirname "$source")" -o "$build/$module.olean" "$source"
}
compile "$repo/graffiti-177/Short177.lean"
compile "$repo/graffiti-177/Proof177.lean"
compile "$repo/graffiti-169/Proof169.lean"
compile "$repo/graffiti-179/Proof179.lean"
compile "$here/Counterexample186.lean"
compile "$here/External186.lean"
