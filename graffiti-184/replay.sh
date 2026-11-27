#!/usr/bin/env bash
# Run from a Lean 4.19 / Mathlib 4.19 project with lake env.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(dirname "$here")"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
lean --version
compile() {
  local src="$1"
  lean -DwarningAsError=true --root="$(dirname "$src")" -o "$build/$(basename "$src" .lean).olean" "$src"
}
compile "$repo/graffiti-185/Counterexample185.lean"
compile "$here/Counterexample184.lean"
