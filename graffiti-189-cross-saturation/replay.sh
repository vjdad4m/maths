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
build "$root/graffiti-189-order-sixteen/src" TraceableOrderSixteen189
prior="$root/graffiti-189-order17-three-off"
(cd "$prior/src" && sha256sum -c ../sources.sha256)
build "$prior/src" OffThree17LongerBase189
for m in 2_5 2_6 2_7 2_8 2_9 2_10 2_11 3_6 3_7 3_8 3_9 3_10 4_7 4_8 4_9 5_8; do
  build "$prior/src" "OffThree17LongerRow${m}189"
done
for m in OffThree17LongerTable189 OrderSeventeenStructural189 OrderSeventeenFoundationLink189 OffThree17Graph189 OffThree17Close189 Order17ThreeBranches189; do
  build "$prior/src" "$m"
done
priorSix="$root/graffiti-189-order17-six-off"
(cd "$priorSix/src" && sha256sum -c ../sources.sha256)
for m in SixCoreMarkedPath189 OffSix17CoreLift189 OffSix17Close189 Order17TwoBranches189; do
  build "$priorSix/src" "$m"
done
priorFive="$root/graffiti-189-order17-five-off"
(cd "$priorFive/src" && sha256sum -c ../sources.sha256)
for m in OffFive17CentralStructure189 OffFive17CentralTransfers189 OffFive17SingletonBase189; do build "$priorFive/src" "$m"; done
for j in 5 6 8 9 10; do build "$priorFive/src" "OffFive17SingletonRow${j}189"; done
for m in OffFive17SingletonTable189 OffFive17SingletonGraph189 OffFive17MarkedCoreBase189; do build "$priorFive/src" "$m"; done
for c in 00012 00112 00122 01112 01122 01222 11112 11122 11222 12222; do build "$priorFive/src" "OffFive17MarkedRow${c}189"; done
for m in OffFive17MarkedTable189 OffFive17MarkedGraph189 OffFive17Close189 Order17OneBranch189; do build "$priorFive/src" "$m"; done
prior17="$root/graffiti-189-order-seventeen"
(cd "$prior17/src" && sha256sum -c ../sources.sha256)
build "$prior17/src" OffFour17Base189
for z in 3_6 3_7 3_8 3_9 4_7 4_8; do build "$prior17/src" "OffFour17Row3_${z}189"; done
for m in OffFour17DiscTable189 OffFour17Structure189 OffFour17GraphLift189 OffFour17Forward189 OffFour17Partition189 OffFour17Close189; do build "$prior17/src" "$m"; done
(cd "$here/src" && sha256sum -c ../sources.sha256)
for m in CrossSaturation189 ForeignSaturation189 NearForeignSaturation189 AdjacentCut189 OddPortsCut189 DistanceTwoCut189; do build "$here/src" "$m"; done

# Recover the published structural branches in one object directory.
for pkg in graffiti-189-four-vertex-side graffiti-189-distance-three graffiti-189-two-cut; do
  folder="$root/$pkg"
  while IFS= read -r name; do
    [[ -f "$obj/$name.olean" ]] || build "$folder/src" "$name"
  done < "$folder/modules.txt"
done
[[ -f "$obj/Rigidity189.olean" ]] || build "$root/graffiti-189/src" Rigidity189
while IFS= read -r name; do build "$root/graffiti-189-near/src" "$name"; done < "$root/graffiti-189-near/modules.txt"
for name in CutExtraction189 DegreeFourTwoConnected189; do build "$here/src" "$name"; done
