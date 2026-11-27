#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
archive=$(realpath "${SIMPLICIAL_ARCHIVE:-$here/../graffiti-384b-joint17/graff384b-joint17-sources.zip}")
[[ $(sha256sum "$archive" | cut -d' ' -f1) == 9d48b8f73ae4711ccc7cdc60d781bbb7106f7fdd53eb3b478d9afb18bc310b3e ]]
export CROSSFOUR_LEAN_BIN=$(realpath "${CROSSFOUR_LEAN_BIN:-$here/../graff384b-codex/.deps/lean-4.19.0-linux/bin}")
export CROSSFOUR_MATHLIB=$(realpath "${CROSSFOUR_MATHLIB:-$here/../graff384b-codex/.deps/mathlib4}")
cd "$here"
stage=$(mktemp -d "$here/.simplicial.XXXXXXXX")
echo "Simplicial build $stage"
unzip -q "$archive" -d "$stage"
(cd "$stage" && sha256sum -c graff384b-joint17/DELIVERY.sha256)
old="$stage/graff384b-joint17"
case "${1:---cold}" in
  --checked-249)
    [[ $# == 3 ]]
    baseLog=$(realpath "$2")
    export ANCHOR_BASE_LOG=$(realpath "$3")
    bash "$old/replay.sh" --checked-249 "$baseLog" "$ANCHOR_BASE_LOG" | tee "$stage/prior.log"
    ;;
  --checked-base)
    [[ $# == 2 ]]
    export ANCHOR_BASE_LOG=$(realpath "$2")
    bash "$old/replay.sh" --checked-base "$ANCHOR_BASE_LOG" | tee "$stage/prior.log"
    ;;
  --cold)
    [[ $# -le 1 ]]
    bash "$old/replay.sh" --cold | tee "$stage/prior.log"
    ;;
  *) echo "Usage: bash replay.sh [--cold | --checked-base Strict166.log | --checked-249 Strict249.log Strict166.log]" >&2; exit 2;;
esac
rg '^Complete joint ear replay verified: 254 graph modules and 615 axiom reports\.' "$stage/prior.log"
joint=$(sed -n 's/^Joint ear build //p' "$stage/prior.log")
weighted=$(sed -n 's/^Weighted repair build //p' "$joint/prior.log")
ports=$(sed -n 's/^Clique attachment build //p' "${baseLog:-$weighted/prior.log}")
export PORTS_BASE_LOG="$ports/prior.log"
export PORTS_SRC="$stage/new"
mkdir -p "$PORTS_SRC/build"
for name in PortFrame29 PortClique29 PortRepair29 Weighted29 RankRepair29 JointEarSample JointEarRank JointEarWitness; do
  cp "$joint/new/build/$name.olean" "$PORTS_SRC/build/"
done
sha256sum -c NEW-SOURCES.sha256
cmp SOURCES.sha256 <(cat "$old/SOURCES.sha256" NEW-SOURCES.sha256)
for name in SimplicialTrial SimplicialRanks IndependentFrontier ReservedRanks AnchorScores IndependentThirteen TwelveWitness; do
  cp "$name.lean" "$PORTS_SRC/"
  bash "$weighted/graff384b-ports29/unit.sh" "$name" 2>&1 | tee "$PORTS_SRC/$name.log"
done
python3 "$here/audit.py" "$PORTS_SRC"
echo 'Complete simplicial replay verified: 261 graph modules and 629 axiom reports.'
