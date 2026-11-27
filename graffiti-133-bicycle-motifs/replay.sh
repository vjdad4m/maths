#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
build="$(mktemp -d)"
trap 'rm -rf "$build"' EXIT
export LEAN_PATH="$build${LEAN_PATH:+:$LEAN_PATH}"
export MALLOC_ARENA_MAX=2
lean --version
for pkg in graffiti-133-density graffiti-133-floor-three graffiti-133-real-three graffiti-133-five-free graffiti-133-seven-cycle graffiti-133-induced-seven graffiti-133-induced-eight graffiti-133-full-four; do
  dir="$here/../$pkg"
  while IFS= read -r module; do
    [[ ! -e "$build/$module.olean" ]] || continue
    lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$dir/src" -o "$build/$module.olean" "$dir/src/$module.lean"
  done < "$dir/modules.txt"
done
src="$build/src"
mkdir "$src"
cp "$here"/src/*.lean "$src/"
python3 "$here/generate_bicycle.py" "$src"
(cd "$src" && sha256sum -c "$here/capsules.sha256")
run() {
  local t="$1"
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true --root="$src" -o "$build/$t.olean" "$src/$t.lean"
}
for m in BicycleCheck133 BicycleRotate133 BicycleHoleLift133 BicycleShapeCheck133 BicycleKeys133; do
  run "$m"
done
for file in "$src"/BicycleTheta*.lean "$src"/BicycleDumb*.lean; do
  name="$(basename "$file" .lean)"
  run "$name"
done
run BicycleShapeCatalog133
