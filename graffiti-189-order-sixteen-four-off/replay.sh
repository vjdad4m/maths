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
while IFS= read -r module; do
  run graffiti-189-order-thirteen "$module"
done < "$here/../graffiti-189-order-thirteen/modules.txt"
src="$here/src"
generated="$obj/generated"
build() {
  local root="$1" m="$2"
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$root" \
    -o "$obj/$m.olean" "$root/$m.lean"
}
export MALLOC_ARENA_MAX=2
build "$src" SoloFastBaseVerified
python3 "$here/generate_solo.py" "$generated" > "$obj/solo-modules"
(cd "$generated" && sha256sum -c "$here/generated.sha256")
while IFS= read -r m; do build "$generated" "$m"; done < "$obj/solo-modules"
build "$src" SoloAllRows
for m in FourOffTwinModel189 FourOffTwinRows189 FourOffSoloExtras189 FourOffGraphSupport189 FourOffGraphCore189 FourOffTwinMarks189 FourOffTwinCompat189 FourOffTwinMixed189 FourOffTwinBoundary189 FourOffTwinGraph189 FourOffSoloGraph189 FourOffComplete189; do
  build "$src" "$m"
done
