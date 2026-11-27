#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
obj="$(mktemp -d)"
trap 'rm -rf "$obj"' EXIT
export LEAN_PATH="$obj${LEAN_PATH:+:$LEAN_PATH}"
export MALLOC_ARENA_MAX=2
lean --version
run() {
  local package="$1" module="$2"
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$here/../$package/src" \
    -o "$obj/$module.olean" "$here/../$package/src/$module.lean"
}
run graffiti-189-four-vertex-side SmallSeparator189
run graffiti-189 Rigidity189
run graffiti-189-degree-four OneSlack189
run graffiti-189-degree-four MultiPinRotation189
for module in PairedOn189 PairedOff189 PairedOnClose189 NoPairs189; do
  run graffiti-189-order-eleven "$module"
done
run graffiti-189-order-twelve TinyFourOrder12189
while IFS= read -r module; do
  [[ "$module" != SmallOrderFour189 ]] || continue
  run graffiti-189-order-thirteen "$module"
done < "$here/../graffiti-189-order-thirteen/modules.txt"
run graffiti-189-order-fourteen-shape TinyFourOrder14Three
while IFS= read -r module; do
  [[ "$module" != FullFourteen189 ]] || continue
  run graffiti-189-order-fourteen "$module"
done < "$here/../graffiti-189-order-fourteen/modules.txt"
for m in OffFour15ReorderedBase OffFour15RowGroup1 OffFour15RowGroup2 OffFour15RowGroup3 OffFour15RowGroup4 OffFour15PinJoin; do
  run graffiti-189-order-fifteen-four-off "$m"
done
proof="$obj/FullFifteen189.lean"
printf '%s\n' 'import OffFour15PinJoin' 'import GraffitiSmallCoreFive' 'import OffThree16InteriorVerified' > "$proof"
sed '$d' "$here/../graffiti-189-order-fourteen/src/FullFourteen189.lean" >> "$proof"
cat "$here/../graffiti-189-order-fifteen-three-off/src/FourOffTwoPinShapeVerified.leanpart" >> "$proof"
while IFS= read -r p; do cat "$here/../graffiti-189-order-fifteen-four-off/src/$p" >> "$proof"; done < "$here/../graffiti-189-order-fifteen-four-off/parts.txt"
for p in ConnectedSaturationVerified LayerCollapseVerified InactiveCoreVerified SixOffFinishVerified; do
  cat "$here/../graffiti-189-saturated/src/$p.leanpart" >> "$proof"
done
for p in FiveOffLengthNineSinglePinVerified FiveOffLengthNineFinishVerified; do
  cat "$here/../graffiti-189-order-fifteen-five-off/src/$p.leanpart" >> "$proof"
done
cat "$here/../graffiti-189-order-fifteen-three-off/src/ThreeOffFifteenVerified.leanpart" >> "$proof"
cat "$here/../graffiti-189-order-fifteen/src/UniqueOmissionNoEnumerationVerified.leanpart" "$here/../graffiti-189-order-fifteen/src/TraceableOrderFifteenAssemblyVerified.leanpart" >> "$proof"
run graffiti-189-order-sixteen-saturated GraffitiSmallCoreFive
run graffiti-189-order-sixteen-shape OffThree16InteriorVerified
cat "$here/../graffiti-189-order-sixteen-saturated/src/SevenOffFinishVerified.leanpart" >> "$proof"
while IFS= read -r p; do cat "$here/src/$p.leanpart" >> "$proof"; printf "\n" >> "$proof"; done < "$here/parts.txt"
echo 'end Graffiti189LongestPath.TwoCut.SmallOrderFour' >> "$proof"
lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$obj" "$proof"
