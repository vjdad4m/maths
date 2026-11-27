#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/.." && pwd)"
obj="$(mktemp -d)"
trap 'rm -rf "$obj"' EXIT
export GRAFF189_REPLAY_OBJ="$obj"
export LEAN_PATH="$obj${LEAN_PATH:+:$LEAN_PATH}"
export MALLOC_ARENA_MAX=2
lean --version

# Reuse the repository's existing ingredient lists and certificate generators.
# Only the object directory and the flattened foundation's external name change.
# The original component scripts are not edited.
shared() {
  local package="$1" shape="${2:-no}"
  python3 - "$root/$package/replay.sh" "$shape" > "$obj/$package-replay.sh" <<'PY'
import pathlib, sys
p, shape = pathlib.Path(sys.argv[1]), sys.argv[2] == "yes"
s = p.read_text()
s = s.replace('here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"', 'here="$GRAFF189_REPLAY_HERE"')
s = s.replace('obj="$(mktemp -d)"', 'obj="$GRAFF189_REPLAY_OBJ"')
s = s.replace("trap 'rm -rf \"$obj\"' EXIT\n", "")
s = s.replace('generated="$obj/generated"', 'generated="$obj/' + p.parent.name + '-generated"')
# In a fresh shared tree repeated named inputs are identical public source files.
s = s.replace('  local package="$1" module="$2"\n', '  local package="$1" module="$2"\n  [[ ! -f "$obj/$module.olean" ]] || return 0\n')
if shape:
    s = s.replace('proof="$obj/FullFifteen189.lean"', 'proof="$obj/OrderSixteenFoundation189.lean"')
    line = 'lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$obj" "$proof"'
    replacement = '''sed -i -e 's/^namespace Graffiti189LongestPath\\.TwoCut\\.SmallOrderFour$/namespace Graffiti189LongestPath.TwoCut.OrderSixteenFoundation/' -e 's/^end Graffiti189LongestPath\\.TwoCut\\.SmallOrderFour$/end Graffiti189LongestPath.TwoCut.OrderSixteenFoundation/' "$proof"
lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$obj" -o "$obj/OrderSixteenFoundation189.olean" "$proof"'''
    assert s.count(line) == 1
    s = s.replace(line, replacement)
assert 'here="$GRAFF189_REPLAY_HERE"' in s
assert 'obj="$GRAFF189_REPLAY_OBJ"' in s
print(s, end="")
PY
  GRAFF189_REPLAY_HERE="$root/$package" bash "$obj/$package-replay.sh"
}

build() {
  local source="$1" module="$2"
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true \
    --root="$source" -o "$obj/$module.olean" "$source/$module.lean"
}

shared graffiti-189-order-sixteen-four-off
shared graffiti-189-five-off-connected-single
shared graffiti-189-order-sixteen-shape yes
build "$here/src" TraceableOrderSixteen189
