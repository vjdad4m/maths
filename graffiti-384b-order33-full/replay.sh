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
pendant="$here/../graffiti-384b-pendant16"
(cd "$pendant"; sha256sum -c NEW-SOURCES.sha256)
for name in PendantSample PendantBound; do
  cp "$pendant/$name.lean" "$PORTS_SRC/"
  bash "$weighted/graff384b-ports29/unit.sh" "$name"
done
for pkg in "$here/../graffiti-384b-adjacent-full" "$here/../graffiti-384b-independent-small" "$here/../graffiti-384b-leaf-full" "$here"; do
  (cd "$pkg"; sha256sum -c sources.sha256)
  while read -r name; do
    cp "$pkg/src/$name.lean" "$PORTS_SRC/"
    bash "$weighted/graff384b-ports29/unit.sh" "$name"
  done < "$pkg/modules.txt"
done
