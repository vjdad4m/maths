#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
mkdir -p "$out/Cases"
export LEAN_PATH="$out:$(lake env printenv LEAN_PATH)"
build() { lean -j1 -DwarningAsError=true --root="$PWD" -o "$out/$1.olean" "$1.lean"; }
build Threshold
for k in $(seq 0 23); do build "Cases/K$k"; done
build Verified
build Base7
build Main7
