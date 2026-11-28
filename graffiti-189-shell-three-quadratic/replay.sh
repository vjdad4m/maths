#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")" && pwd)
obj=$(mktemp -d)
trap 'rm -rf "$obj"' EXIT
echo '== StandaloneShellQuadratic189 =='
lean -j1 -DElab.async=false -DwarningAsError=true --root="$root" \
  -o "$obj/StandaloneShellQuadratic189.olean" "$root/StandaloneShellQuadratic189.lean"
