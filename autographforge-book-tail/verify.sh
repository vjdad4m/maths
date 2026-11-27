#!/usr/bin/env bash
set -euo pipefail

proof_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
workspace="$(cd "$proof_dir/../.." && pwd)"
mathlib_dir="${MATHLIB_DIR:-$workspace/batch_comb/mathlib4}"
lean_bin_dir="${LEAN_BIN_DIR:-$workspace/wow108/lean-4.19.0-linux/bin}"
if [[ -d "$lean_bin_dir" ]]; then
  export PATH="$lean_bin_dir:$PATH"
fi
cd "$mathlib_dir"
version="$(lean --version)"
echo "$version"
[[ "$version" == "Lean (version 4.19.0,"* ]]
[[ "$(cat lean-toolchain)" == "leanprover/lean4:v4.19.0" ]]
[[ "$(git rev-parse HEAD)" == "c44e0c8ee63ca166450922a373c7409c5d26b00b" ]]
export LEAN_PATH="$PWD/.lake/build/lib/lean"
for package_lib in "$PWD"/.lake/packages/*/.lake/build/lib/lean; do
  LEAN_PATH="$LEAN_PATH:$package_lib"
done
lean -DwarningAsError=true "--root=$proof_dir" "$proof_dir/BookTail.lean"
