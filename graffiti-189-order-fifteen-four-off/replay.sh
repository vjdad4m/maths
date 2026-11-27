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
for m in OffFour15ReorderedBase OffFour15RowGroup1 OffFour15RowGroup2 OffFour15RowGroup3 OffFour15RowGroup4 OffFour15PinJoin; do
  run graffiti-189-order-fifteen-four-off "$m"
done
printf '%s\n' 'import OffFour15PinJoin' > "$obj/FourOffFifteen189.lean"
sed '$d' "$here/../graffiti-189-order-fourteen-shape/src/ShapeFourteen189.lean" >> "$obj/FourOffFifteen189.lean"
cat "$here/../graffiti-189-order-fifteen-three-off/src/FourOffTwoPinShapeVerified.leanpart" >> "$obj/FourOffFifteen189.lean"
while IFS= read -r part; do cat "$here/src/$part" >> "$obj/FourOffFifteen189.lean"; done < "$here/parts.txt"
echo 'end Graffiti189LongestPath.TwoCut.SmallOrderFour' >> "$obj/FourOffFifteen189.lean"
lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$obj" "$obj/FourOffFifteen189.lean"
