#!/usr/bin/env bash
set -euo pipefail
current="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export KELMANS_RANKED_CURRENT="$current"
prior="$current/../kelmans-remote-t2-bridge"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
python3 - "$prior/replay.sh" "$tmp/full.sh" <<'PY'
from pathlib import Path
import sys
a,b=map(Path,sys.argv[1:])
s=a.read_text()
old='here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"'
assert s.count(old)==1
s=s.replace(old,'here="$KELMANS_RANKED_CURRENT/../kelmans-remote-t2-bridge"')
b.write_text(s+'''
here="$KELMANS_RANKED_CURRENT"
for p in kelmans-defect kelmans-defect-cyclic; do
  while IFS= read -r m; do
    [[ -f "$obj/$m.olean" ]] || run "$p" "$m"
  done < "$here/../$p/modules.txt"
done
for m in Handle189 HandleCuts; do run kelmans-handle "$m"; done
(cd "$here/src" && sha256sum -c ../sources.sha256)
while IFS= read -r m; do run kelmans-remote-t2-ranked-cuts "$m"; done < "$here/modules.txt"
''')
PY
bash "$tmp/full.sh"
