#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export GRAFF189_R5_CURRENT="$here"
root="$(dirname "$here")"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
python3 - "$root/graffiti-189-cross-saturation/replay.sh" "$tmp/run.sh" <<'PY'
from pathlib import Path
import sys
a,b=map(Path,sys.argv[1:])
s=a.read_text()
old='here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"'
assert s.count(old) == 1
s=s.replace(old,'here="$GRAFF189_R5_CURRENT/../graffiti-189-cross-saturation"')
b.write_text(s+'''
for p in "$root/graffiti-189-complete-degree-four" "$GRAFF189_R5_CURRENT"; do
  (cd "$p/src" && sha256sum -c ../sources.sha256)
  while IFS= read -r m; do build "$p/src" "$m"; done < "$p/modules.txt"
done
''')
PY
bash "$tmp/run.sh"
