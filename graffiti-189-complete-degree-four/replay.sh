#!/usr/bin/env bash
set -euo pipefail
current="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export GRAFF189_R4_CURRENT="$current"
prior="$current/../graffiti-189-cross-saturation"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
python3 - "$prior/replay.sh" "$tmp/full.sh" <<'PY'
from pathlib import Path
import sys
prior, target=map(Path,sys.argv[1:])
s=prior.read_text()
old='here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"'
assert s.count(old)==1
s=s.replace(old,'here="$GRAFF189_R4_CURRENT/../graffiti-189-cross-saturation"')
target.write_text(s+'''
current="$GRAFF189_R4_CURRENT"
(cd "$current/src" && sha256sum -c ../sources.sha256)
while IFS= read -r module; do build "$current/src" "$module"; done < "$current/modules.txt"
''')
PY
bash "$tmp/full.sh" | tee "$tmp/replay.log"
grep -Fxq "'Graffiti189LongestPath.CrossSaturation.traceable_degree_four' depends on axioms: [propext, Classical.choice, Quot.sound]" "$tmp/replay.log"
