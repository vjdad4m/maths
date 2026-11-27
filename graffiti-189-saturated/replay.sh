#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
obj="$(mktemp -d)"
trap 'rm -rf "$obj"' EXIT
export LEAN_PATH="$obj${LEAN_PATH:+:$LEAN_PATH}"
lean --version
run() {
  local package="$1" module="$2"
  lean -j1 -DwarningAsError=true --root="$here/../$package/src" \
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
sed '$d' "$here/../graffiti-189-order-fourteen-shape/src/ShapeFourteen189.lean" > "$obj/Saturated189.lean"
for part in ConnectedSaturationVerified LayerCollapseVerified InactiveCoreVerified SixOffFinishVerified; do
  cat "$here/src/$part.leanpart" >> "$obj/Saturated189.lean"
done
echo 'end Graffiti189LongestPath.TwoCut.SmallOrderFour' >> "$obj/Saturated189.lean"
lean -j1 -DwarningAsError=true --root="$obj" "$obj/Saturated189.lean"
