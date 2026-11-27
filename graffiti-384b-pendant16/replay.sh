#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
stage=$(mktemp -d "${PENDANT_BUILD_PARENT:-$here}/.pendant.XXXXXXXX")
echo "Pendant build $stage"
bin=$(realpath "${CROSSFOUR_LEAN_BIN:-$here/../graff384b-codex/.deps/lean-4.19.0-linux/bin}")
mathlib=$(realpath "${CROSSFOUR_MATHLIB:-$here/../graff384b-codex/.deps/mathlib4}")
export CROSSFOUR_LEAN_BIN="$bin" CROSSFOUR_MATHLIB="$mathlib"
"$bin/lean" --version | grep '4.19.0'
cd "$here"
archive="${PENDANT_WEIGHTED_ARCHIVE:-$stage/graff384b-weighted29-sources.zip}"
if [[ -z "${PENDANT_WEIGHTED_ARCHIVE:-}" ]]; then
  unzip -p "$here/../graffiti-384b-joint17/graff384b-joint17-sources.zip" graff384b-weighted29/graff384b-weighted29-sources.zip > "$archive"
fi
printf '%s  %s\n' 5f417c93ded057fcc6d3bafb4d38dbab5c3269adacd37fac1cdff1b3d3c949c1 "$archive" | sha256sum -c -
sha256sum -c NEW-SOURCES.sha256
unzip -q "$archive" -d "$stage"
base="$stage/graff384b-weighted29"
(cd "$stage" && sha256sum -c graff384b-weighted29/DELIVERY.sha256)
case "${1:---cold}" in
 --cold)
    [[ $# -le 1 ]]
    log="$stage/prior.log"
    bash "$base/replay.sh" --cold | tee "$log" ;;
 --checked-251)
    [[ $# == 2 ]]
    log=$(realpath "$2")
    export ANCHOR_BASE_LOG=${ANCHOR_BASE_LOG:-"$here/../graff384b-ear-exchange/Strict166.log"}
    cmp "$log" "$base/Strict251.log" ;;
 *) echo 'Usage: bash replay.sh [--cold | --checked-251 /absolute/path/to/Strict251.log]' >&2; exit 2 ;;
esac
rg '^Complete weighted repair replay verified: 251 graph modules and 606 axiom reports\.' "$log"
weighted=$(sed -n 's/^Weighted repair build //p' "$log")
python3 "$base/audit.py" "$weighted/new"
prior="$weighted/prior.log"
[[ -f "$prior" ]] || prior="$weighted/graff384b-ports29/Strict249.log"
ports=$(sed -n 's/^Clique attachment build //p' "$prior")
export PORTS_BASE_LOG="$ports/prior.log"
export PORTS_SRC="$stage/new"
mkdir -p "$PORTS_SRC/build"
if [[ ${1:---cold} == --checked-251 ]]; then
 (cd "$weighted/new/build" && sha256sum -c "$here/CHECKED-OBJECTS.sha256")
fi
for name in PortFrame29 PortClique29 PortRepair29 Weighted29 RankRepair29; do
 cp "$weighted/new/build/$name.olean" "$PORTS_SRC/build/"
done
for name in PendantSample PendantBound; do
 cp "$name.lean" "$PORTS_SRC/"
 bash "$weighted/graff384b-ports29/unit.sh" "$name" 2>&1 | tee "$PORTS_SRC/$name.log"
done
python3 "$here/audit.py" "$PORTS_SRC"
