#!/usr/bin/env bash
set -euo pipefail
current246="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
current244="$current246/../graffiti-384b-rich-degree31"
latest="$current244/../graffiti-384b-five-clique-free31"
next="$latest/../graffiti-384b-ear-cubic31"
current="$next/../graffiti-384b-diversity31"
here="$current/../graffiti-384b-diversity33"
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
archived="$here/../graffiti-384b-leaf-ear"
while IFS= read -r m; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$archived/src" \
    -o "$tmp/new/$m.olean" "$archived/src/$m.lean"
done < "$archived/modules.txt"
prior="$here/../graffiti-384b-ear-exchange"
for m in Exchange33 EarFrame33 EarAttachment33 EarRoot33 EarOnClique33 EarFixture33; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$prior" \
    -o "$tmp/new/$m.olean" "$prior/$m.lean"
done
(cd "$here/../graffiti-384b-cubic-ear-anchor" && sha256sum -c NEW-SOURCES.sha256)
for m in AnchorDeletion33 AnchorCut33 CubicAnchor33 ParityAnchor33 FinishAnchor33 AnchorEdge33; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$here/../graffiti-384b-cubic-ear-anchor" \
    -o "$tmp/new/$m.olean" "$here/../graffiti-384b-cubic-ear-anchor/$m.lean"
done
parent="$here/../graffiti-384b-cubic-ear-closure"
(cd "$parent" && sha256sum -c NEW-SOURCES.sha256)
for m in ResidualArms33 ResidualLongest33 ResidualContacts33 CubicDiamondCut33 CubicClosure33 CubicCoreStrict33 CubicSquareProfile33; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$parent" \
    -o "$tmp/new/$m.olean" "$parent/$m.lean"
done
high="$here/../graffiti-384b-high-ears"
(cd "$high" && sha256sum -c NEW-SOURCES.sha256)
for m in HighEarPins33 HighEarShared33 HighEarDegree33 HighEarSwitch33 HighEarBypass33 HighEarParity33 HighEarOdd33 HighEarLayout33 HighEarDetour33 HighEarFinish33 HighEarRootCap33; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$high" \
    -o "$tmp/new/$m.olean" "$high/$m.lean"
done
palette="$here/../graffiti-384b-ear-palette"
(cd "$palette" && sha256sum -c NEW-SOURCES.sha256)
for m in PaletteContact33 PaletteFibers33 PaletteSample33 PaletteFinish33; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$palette" \
    -o "$tmp/new/$m.olean" "$palette/$m.lean"
done
cubic="$here/../graffiti-384b-cubic-root"
(cd "$cubic" && sha256sum -c NEW-SOURCES.sha256)
for m in PrivateCut33 PrivateShores33 PrivatePivot33 PrivatePairs33 PrivatePalette33 PrivateFrame33 CubicRootFinish33 ZeroNeighbor33; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$cubic" \
    -o "$tmp/new/$m.olean" "$cubic/$m.lean"
done
(cd "$here" && sha256sum -c NEW-SOURCES.sha256)
for m in SupportedEar33 BothCubics33 FullScorePair33 CliqueCubicCover33 SharedTransversal33 SharedSample33 SharedSaving33 CubicOverlap33 FullObstruction33 DiamondFree33 ThreeFibers33 ThreeBudget33 ThreeGeometry33 ThreeFinish33 Diversity33Finish; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$here" \
    -o "$tmp/new/$m.olean" "$here/$m.lean"
done
(cd "$current" && sha256sum -c NEW-SOURCES.sha256)
for m in FrontierSample31 FrontierProfile31 FrontierCore31 FrontierPivot31 Frontier31Finish FrontierTable31 FrontierDegrees31 FrontierRoots31 Diversity31Frontier; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$current" -o "$tmp/new/$m.olean" "$current/$m.lean"
done
(cd "$next" && sha256sum -c NEW-SOURCES.sha256)
for m in SevenFibers SevenBudget SevenModel SevenTrial SevenContact SevenEmbedding SevenFinish; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$next" -o "$tmp/new/$m.olean" "$next/$m.lean"
done
(cd "$latest" && sha256sum -c NEW-SOURCES.sha256)
for m in CreditTrial31 CreditRanks31 CreditProfile31 CreditEnds31 CreditGeometry31 CreditTable31 CreditSampling31 CreditFinish31; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$latest" -o "$tmp/new/$m.olean" "$latest/$m.lean"
done
(cd "$current244" && sha256sum -c NEW-SOURCES.sha256)
for m in CoverCut31 CoverClique31 CoverDense31; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$current244" -o "$tmp/new/$m.olean" "$current244/$m.lean"
done
(cd "$current246" && sha256sum -c NEW-SOURCES.sha256)
for m in SquareFrame29 SquareTriple29; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$current246" -o "$tmp/new/$m.olean" "$current246/$m.lean"
done
