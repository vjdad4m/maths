#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
export CROSSFOUR_MATHLIB="${CROSSFOUR_MATHLIB:?Set this to a prepared Mathlib 4.19.0 checkout}"
export CROSSFOUR_LEAN_BIN="${CROSSFOUR_LEAN_BIN:?Set this to the Lean 4.19.0 bin directory}"
mkdir "$tmp/upstream-order34"
cp "$here/../graffiti-384b-two-ears/"*.py "$here/../graffiti-384b-two-ears/src/"*.lean "$tmp/"
python3 - "$here/../graffiti-384b-order34" "$tmp/upstream-order34" <<'PY'
import base64, hashlib, io, re, sys, tarfile
from pathlib import Path
old, dest = map(Path, sys.argv[1:])
for file in ("modules.txt","sha256sums.txt"):
    (dest/file).write_bytes((old/file).read_bytes())
digest = {l.split()[1]:l.split()[0] for l in (dest/"sha256sums.txt").read_text().splitlines()}
archive = base64.b64decode((old/"lean-dependencies.tar.gz.b64").read_bytes())
with tarfile.open(fileobj=io.BytesIO(archive),mode="r:gz") as t:
    seen = set()
    for f in t:
        if not f.isfile() or not re.fullmatch(r"[A-Za-z0-9_]+\.lean", f.name) or f.name in seen:
            raise ValueError(f.name)
        seen.add(f.name)
        data = t.extractfile(f).read()
        if hashlib.sha256(data).hexdigest()!=digest[f.name]:
            raise ValueError(f.name)
        (dest/f.name).write_bytes(data)
for name, expected in digest.items():
    if not (dest/name).exists():
        data=(old/"src"/name).read_bytes()
        if hashlib.sha256(data).hexdigest()!=expected:
            raise ValueError(name)
        (dest/name).write_bytes(data)
PY
python3 -B "$tmp/crossfour_replay.py"

obj=("$tmp"/.crossfour34.*)
[[ ${#obj[@]} == 1 && -d "${obj[0]}" ]]
export PATH="$CROSSFOUR_LEAN_BIN:$PATH"
mathlib="$(realpath "$CROSSFOUR_MATHLIB")"
leanpath="$(cd "$mathlib" && lake env printenv LEAN_PATH)"
export LEAN_PATH="$tmp/new:${obj[0]}"
IFS=: read -ra deps <<< "$leanpath"
for dep in "${deps[@]}"; do
  if [[ "$dep" != /* ]]; then dep="$mathlib/$dep"; fi
  LEAN_PATH="$LEAN_PATH:$dep"
done
mkdir "$tmp/new"
for m in OneEarCycle384b OneEarCut384b OneEarRoute384b OneEarFinish384b; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$here/../graffiti-384b-one-ear/src" \
    -o "$tmp/new/$m.olean" "$here/../graffiti-384b-one-ear/src/$m.lean"
done
while IFS= read -r m; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$here/src" \
    -o "$tmp/new/$m.olean" "$here/src/$m.lean"
done < "$here/modules.txt"
