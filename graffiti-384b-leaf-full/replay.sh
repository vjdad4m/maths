#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
base="$here/../graffiti-384b-independent13"
bash "$base/replay.sh" --cold | tee "$tmp/base.log"
simp=$(sed -n 's/^Simplicial build //p' "$tmp/base.log")
joint=$(sed -n 's/^Joint ear build //p' "$simp/prior.log")
weighted=$(sed -n 's/^Weighted repair build //p' "$joint/prior.log")
ports=$(sed -n 's/^Clique attachment build //p' "$weighted/prior.log")
export PORTS_BASE_LOG="$ports/prior.log"
export PORTS_SRC="$tmp/new"
mkdir -p "$PORTS_SRC/build"
cp "$simp/new/build/"*.olean "$PORTS_SRC/build/"
for stage in "$here/../graffiti-384b-independent-small" "$here"; do
  (cd "$stage"; sha256sum -c sources.sha256)
  while read -r name; do
    cp "$stage/src/$name.lean" "$PORTS_SRC/"
    bash "$weighted/graff384b-ports29/unit.sh" "$name"
  done < "$stage/modules.txt"
done
