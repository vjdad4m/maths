#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(cd "${1:-$here/..}" && pwd)"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
lean --version | grep -F 'version 4.19.0'
compile() {
  local module="$1" src="$2"
  lean -j1 -s16384 -DElab.async=false -DwarningAsError=true --root="$src" -o "$build/$module.olean" "$src/$module.lean"
}
compile TwinObstruction "$repo/kelmans-twin-obstruction/src"
for module in SquareCapGeometry SquareCapFactor; do
  compile "$module" "$repo/kelmans-square-f2/src"
done
for module in RemoteVacancyReach RemoteMonotoneRank RemoteMonotoneCompletion RemoteMonotoneDependencies RemoteMonotoneShape RemoteVacancySeparation RemoteVacancySeparationMetric; do
  compile "$module" "$here/src"
done
