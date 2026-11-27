#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
obj="$(mktemp -d)"
trap 'rm -rf "$obj"' EXIT
export LEAN_PATH="$obj${LEAN_PATH:+:$LEAN_PATH}"
lean --version
run() {
  local dir="$here/../$1/src" n="$2"
  lean -j1 -s 16384 -DElab.async=false -DwarningAsError=true --root="$dir" -o "$obj/$n.olean" "$dir/$n.lean"
}
run kelmans-square-f2 SquareCapGeometry
run kelmans-square-f2 SquareCapFactor
run kelmans-pentagon-f2 PentagonProfile
run kelmans-pentagon-f2 PentagonCap
for m in SevenPortTheta ThetaExteriorFixture SevenPortObstruction ThetaLocalRoute SevenPortObstructionLayout SevenPortCutCycles; do
  run kelmans-seven-port-cap-obstruction "$m"
done
