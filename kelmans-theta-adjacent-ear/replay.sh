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
for n in PentagonProfile PentagonCap PentagonTransfer; do
  run kelmans-pentagon-f2 "$n"
done
for n in ThetaTransfer ThetaGeometry ThetaModes ThetaCase; do
  run kelmans-theta-f2 "$n"
done
for m in EarTransfer EarDecode FiveCapCut EarCase; do
  run kelmans-theta-ear-reduction "$m"
done
run kelmans-seven-port-cap-obstruction ThetaLocalRoute
for m in ThetaFiveTransferLocal ThetaFiveModes ThetaFiveRing ThetaFiveAssemble ThetaFiveExterior; do
  run kelmans-theta-exterior-avoidance "$m"
done
run kelmans-theta-ear-reduction EarPorts
run kelmans-theta-ear-reduction EarRelease
for m in ThetaAdjacentEarPatch ThetaAdjacentEarLeafModes ThetaAdjacentEarRefill ThetaAdjacentEarStitch ThetaAdjacentEarCap ThetaAdjacentEarOriginal ThetaAdjacentEarMirror ThetaAdjacentEarFixture ThetaAdjacentEarFixtureLayout; do
  run kelmans-theta-adjacent-ear "$m"
done
