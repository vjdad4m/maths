#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
if [[ -n ${LEAN_BIN:-} ]]; then export PATH="$LEAN_BIN:$PATH"; fi
if [[ -n ${MATHLIB_DIR:-} ]]; then
  export LEAN_PATH="$MATHLIB_DIR/.lake/build/lib/lean"
  for lib in "$MATHLIB_DIR"/.lake/packages/*/.lake/build/lib/lean; do export LEAN_PATH="$LEAN_PATH:$lib"; done
fi
lean --version
lean --version | grep -F 'version 4.19.0'
sha256sum --check --status sources.sha256
obj=$(mktemp -d "${TMPDIR:-/tmp}/descent-one-180.XXXXXXXX")
trap 'rm -rf "$obj"' EXIT
mkdir "$obj/foundation"
repo=$(cd "$here/.." && pwd)
while read -r blob path; do
  file="$repo/$path"
  [[ "$(git hash-object "$file")" == "$blob" ]]
  cp "$file" "$obj/foundation/${path##*/}"
done < published-blobs.txt
(cd "$obj" && sha256sum --check --status "$here/foundation.sha256")
export LEAN_PATH="$obj${LEAN_PATH:+:$LEAN_PATH}"
while read -r mod; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$obj/foundation" -o "$obj/$mod.olean" "$obj/foundation/$mod.lean" > "$obj/$mod.log" 2>&1 || { cat "$obj/$mod.log"; exit 1; }
done < foundation.txt
printf 'Recompiled %d pinned foundation modules.\n' "$(wc -l < foundation.txt)"
while read -r mod theorem; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$here" -o "$obj/$mod.olean" "$here/$mod.lean" | tee "$obj/$mod.log"
  lean -j1 -DwarningAsError=true --run "$here/Replay.lean" "$obj/$mod.olean" "$theorem" | tee -a "$obj/$mod.log"
done < modules.txt
python3 audit.py "$obj"
