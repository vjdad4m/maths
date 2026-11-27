#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
base="$here/../graffiti-384b-pendant16"
PENDANT_BUILD_PARENT="$tmp" bash "$base/replay.sh" --cold | tee "$tmp/base.log"
pendant=$(sed -n 's/^Pendant build //p' "$tmp/base.log")
weighted=$(sed -n 's/^Weighted repair build //p' "$pendant/prior.log")
ports=$(sed -n 's/^Clique attachment build //p' "$weighted/prior.log")
export PORTS_BASE_LOG="$ports/prior.log"
export PORTS_SRC="$tmp/new"
mkdir -p "$PORTS_SRC/build"
cp "$pendant/new/build/"*.olean "$PORTS_SRC/build/"
(cd "$here"; sha256sum -c sources.sha256)
while read -r name; do
  cp "$here/src/$name.lean" "$PORTS_SRC/"
  bash "$weighted/graff384b-ports29/unit.sh" "$name"
done < "$here/modules.txt"
