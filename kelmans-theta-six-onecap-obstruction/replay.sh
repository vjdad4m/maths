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
run kelmans-twin-obstruction TwinObstruction
for m in ThetaSevenFaithfulPatch ThetaSevenFaithfulRefill ThetaSevenFaithfulSplice ThetaSevenFaithfulCap ThetaSevenFaithfulFixture; do
  run kelmans-theta-faithful-threecap "$m"
done
run kelmans-theta-six-onecap-obstruction ThetaSevenFaithfulFailedOneCaps
