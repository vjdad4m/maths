#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
lean --version
python3 "$here/c9WitnessGen.py" > "$build/witnesses.txt"
python3 - "$here/src/C9MaskCore133.lean" "$build/witnesses.txt" <<'CHECK_WITNESSES'
import sys
from pathlib import Path
source, witness = [Path(p).read_text() for p in sys.argv[1:]]
assert witness.strip() in source, "regenerated witness table does not match"
CHECK_WITNESSES
for pkg in graffiti-133-density graffiti-133-floor-three graffiti-133-real-three graffiti-133-five-free graffiti-133-seven-cycle graffiti-133-induced-seven graffiti-133-induced-eight graffiti-133-full-four graffiti-133-dominating-nine; do
  dir="$here/../$pkg"
  while IFS= read -r module; do
    [[ ! -e "$build/$module.olean" ]] || continue
    lean -j1 -DwarningAsError=true --root="$dir/src" -o "$build/$module.olean" "$dir/src/$module.lean"
  done < "$dir/modules.txt"
done
