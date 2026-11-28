#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
root=$PWD
sha256sum -c MANIFEST.sha256
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out${LEAN_PATH:+:$LEAN_PATH}"
build() { local f="$1"; lean -j1 -s65536 -DElab.async=false -DwarningAsError=true --root="$(dirname "$f")" -o "$out/$(basename "${f%.lean}").olean" "$f"; }
for m in SixLayer24SlotNumbers189 Equality24ProfileMiddle189 SixLayer24CoverMiddle189 SixLayer24Normalization189 SixLayer24LabelBase189 SixLayer24Slots189 SixLayer24CanonicalPartition189 SixLayer24ChildOrder189 SixLayer24ModelMiddle189 Equality24CNFMiddle189 Equality24CountMiddle189; do
 build "$root/src/$m.lean"
done
for f in "$root"/frames/*.lean; do build "$f"; done
build "$root/src/Equality24Complete189.lean"
build "$root/src/Equality24SecondSmallest189.lean"
