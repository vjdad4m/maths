#!/usr/bin/env bash
set -euo pipefail
next="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export GRAFF133_NEXT="$next"
prior="$next/../graffiti-133-dominating-c7-core"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
python3 - "$prior/replay.sh" "$tmp/replay.sh" <<'PY'
from pathlib import Path
import sys
a,b=map(Path,sys.argv[1:])
s=a.read_text()
old='here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"'
assert s.count(old)==1
s=s.replace(old,'here="$GRAFF133_NEXT/../graffiti-133-dominating-c7-core"')
b.write_text(s+'''
next="$GRAFF133_NEXT"
(cd "$next/src" && sha256sum -c ../sources.sha256)
cp "$next"/src/*.lean "$src/"
while IFS= read -r m; do run "$m"; done < "$next/modules.txt"
''')
PY
bash "$tmp/replay.sh"
