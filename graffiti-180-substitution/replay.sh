#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
if [[ -n ${LEAN_BIN:-} ]]; then export PATH="$LEAN_BIN:$PATH"; fi
: "${MATHLIB_DIR:?Set MATHLIB_DIR to the built, pinned Mathlib checkout.}"
if [[ -n ${MATHLIB_DIR:-} ]]; then
  actual_mathlib=$(git -C "$MATHLIB_DIR" rev-parse HEAD)
  test "$actual_mathlib" = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
  echo "Mathlib commit $actual_mathlib"
  export LEAN_PATH="$MATHLIB_DIR/.lake/build/lib/lean"
  for lib in "$MATHLIB_DIR"/.lake/packages/*/.lake/build/lib/lean; do export LEAN_PATH="$LEAN_PATH:$lib"; done
fi
lean --version
lean --version | grep -F 'version 4.19.0'
repo="$(dirname "$here")"
obj=$(mktemp -d "${TMPDIR:-/tmp}/substitution-180.XXXXXXXX")
trap 'rm -rf "$obj"' EXIT
mkdir -p "$obj/foundation"
while read -r digest source; do
  [[ $(git hash-object "$repo/$source") == "$digest" ]]
  cp "$repo/$source" "$obj/foundation/$(basename "$source")"
done < "$here/published-blobs.txt"
for m in NearestPort180 PortComponents180 PortRecurrence180 DeletedRoot180; do
  cp "$repo/graffiti-180-port-parity/$m.lean" "$obj/foundation/"
done
(cd "$obj" && sha256sum --check --status "$here/foundation.sha256")
sha256sum --check --status sources.sha256
export LEAN_PATH="$obj${LEAN_PATH:+:$LEAN_PATH}"
while read -r mod; do
  lean -j1 -s 65536 -DwarningAsError=true --root="$obj/foundation" -o "$obj/$mod.olean" "$obj/foundation/$mod.lean" > "$obj/$mod.log" 2>&1 || { cat "$obj/$mod.log"; exit 1; }
done < foundation.txt
printf 'Recompiled %d pinned foundation modules.\n' "$(wc -l < foundation.txt)"
while read -r mod theorem; do
  lean -j1 -s 65536 -DwarningAsError=true --root="$here" -o "$obj/$mod.olean" "$here/$mod.lean" | tee "$obj/$mod.log"
  lean -j1 -DwarningAsError=true --run "$here/Replay.lean" "$obj/$mod.olean" "$theorem" | tee -a "$obj/$mod.log"
done < modules.txt
python3 audit.py "$obj"
