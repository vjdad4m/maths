#!/usr/bin/env bash
set -euo pipefail
src=$(cd -- "$(dirname -- "$0")" && pwd)
cd -- "${MATHLIB_DIR:?Set MATHLIB_DIR to Mathlib v4.19.0}"
[[ $(git rev-parse HEAD) == c44e0c8ee63ca166450922a373c7409c5d26b00b ]]
lean=$(lake env which lean)
search=$(lake env printenv LEAN_PATH)
version=$("$lean" --version)
[[ "$version" == *"version 4.19.0,"* ]]
echo "$version"
obj=${CYCLE_BUILD:-$(mktemp -d)}
if [[ -z "${CYCLE_BUILD:-}" ]]; then trap 'rm -rf -- "$obj"' EXIT; fi
mkdir -p "$obj"
export LEAN_PATH="$obj:$search"
for module in "${@}"; do
  "$lean" -j1 --root="$src" -DwarningAsError=true -o "$obj/$module.olean" "$src/$module.lean"
done
