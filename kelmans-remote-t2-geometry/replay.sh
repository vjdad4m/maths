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
run kelmans-theta-faithful-local-cut ThetaSevenFaithfulLocalCut
for m in ThetaSevenFaithfulBoundary ThetaSevenFaithfulCost ThetaSevenFaithfulTiny ThetaSevenFaithfulValid; do
  run kelmans-theta-faithful-cap-validity "$m"
done
(cd "$here/src" && sha256sum -c ../sources.sha256)
for m in RemoteT2Scope RemoteT2PairCounts RemoteT2PairStructure RemoteT2AvoidThree RemoteT2SideCompletionCuts RemoteT2CompletionObstruction14; do
  run kelmans-remote-t2-geometry "$m"
done
