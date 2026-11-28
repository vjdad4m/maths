#!/bin/bash
set -euo pipefail
root=$(cd "$(dirname "$0")" && pwd)
cd "$root"
sha256sum -c SOURCES.sha256
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out${LEAN_PATH:+:$LEAN_PATH}"
for m in SixTwoShoreTen189 SixElevenArithmetic189 SixElevenGeometry189 SixElevenCharges189 SixElevenPartition189 SixElevenClosed189 SixDistanceThreeNineteen189; do
  lean --root="$root" -j1 -s32768 -DElab.async=false -DwarningAsError=true -o "$out/$m.olean" "$root/$m.lean"
done
