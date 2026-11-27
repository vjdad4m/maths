#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
obj="$(mktemp -d)"
trap 'rm -rf "$obj"' EXIT
export LEAN_PATH="$obj${LEAN_PATH:+:$LEAN_PATH}"
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
run graffiti-189-order-twelve SmallOrderFour189
run graffiti-189-order-sixteen-four-off FourOffTwinModel189
run graffiti-189-order-sixteen-four-off FourOffGraphSupport189
run graffiti-189-order-sixteen-four-off FourOffGraphCore189
for m in OffFiveMixedModel189 OffFiveDisconnectedFoundation189 OffFiveMixedShape189 OffFiveLabeling189 OffFiveMixedMarks189 OffFiveMixedClose189; do
  run graffiti-189-five-off-disconnected-mixed "$m"
done
