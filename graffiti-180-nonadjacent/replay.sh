#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/.." && pwd)
old="$repo/graffiti-180-transversals"
stage=$(mktemp -d)
trap 'rm -rf "$stage"' EXIT
mkdir -p "$stage/foundation" "$stage/previous" "$stage/new"
if [[ -n ${LEAN_BIN:-} ]]; then export PATH="$LEAN_BIN:$PATH"; fi
: "${MATHLIB_DIR:?Set MATHLIB_DIR to built pinned Mathlib}"
lean --version | grep -F 'version 4.19.0,'
test "$(git -C "$MATHLIB_DIR" rev-parse HEAD)" = c44e0c8ee63ca166450922a373c7409c5d26b00b
export LEAN_PATH="$stage/new:$stage/previous:$MATHLIB_DIR/.lake/build/lib/lean"
for lib in "$MATHLIB_DIR"/.lake/packages/*/.lake/build/lib/lean; do export LEAN_PATH="$LEAN_PATH:$lib"; done
while read -r blob path; do
  test "$(git hash-object "$repo/$path")" = "$blob"
  cp "$repo/$path" "$stage/foundation/"
done < "$old/published-blobs.txt"
cp "$old/foundation.sha256" "$stage/"
(cd "$stage"; sha256sum --check --status foundation.sha256)
(cd "$old"; sha256sum --check --status sources.sha256)
(cd "$here"; sha256sum --check --status sources.sha256)
run() {
  local root="$1" obj="$2" name="$3"
  lean -j1 -s 65536 -DwarningAsError=true --root="$root" -o "$obj/$name.olean" "$root/$name.lean"
}
while read -r name; do run "$stage/foundation" "$stage/previous" "$name"; done < "$old/foundation.txt"
while read -r name target; do run "$old" "$stage/previous" "$name"; done < "$old/modules.txt"
while read -r name target; do
  run "$here" "$stage/new" "$name"
  lean -j1 -DwarningAsError=true --run "$old/Replay.lean" "$stage/new/$name.olean" "$target"
done < "$here/modules.txt"
