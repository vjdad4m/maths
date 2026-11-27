#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
for m in Core Nodal Perron Energy Block CliqueEdges NearClique Dense Cross FourFifths; do
  src="$m.lean"
  if [[ ! -f "$src" ]]; then src="../cazenave-1-triangle-free/$src"; fi
  lean --root="$(dirname "$src")" -j1 -DElab.async=false -DwarningAsError=true -o "$build/$m.olean" "$src"
done
