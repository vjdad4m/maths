#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "$0")" && pwd)"
obj="$(mktemp -d)"
trap 'rm -rf "$obj"' EXIT
lean -j1 -DElab.async=false -DwarningAsError=true --root="$root" -o "$obj/ThreeShoreCutBound189.olean" "$root/ThreeShoreCutBound189.lean"
