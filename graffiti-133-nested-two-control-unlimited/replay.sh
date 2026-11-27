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
motifs="$here/../graffiti-133-bicycle-motifs"
src="$build/src"
mkdir "$src"
cp "$motifs"/src/*.lean "$src/"
python3 "$motifs/generate_bicycle.py" "$src"
(cd "$src" && sha256sum -c "$motifs/capsules.sha256")
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
cp "$here"/../graffiti-133-figure-eight-exclusion/src/*.lean "$src/"
for m in BicycleChannelPath133 BicycleComponents133 BicycleHubChannels133 BicycleFigureModel133 BicycleFigureBounds133 BicycleFigureCanonical133 BicycleFigureExclude133; do
  run "$m"
done
base="$here/../graffiti-133-singleton-exterior"
cp "$base"/src/*.lean "$src/"
while IFS= read -r m; do run "$m"; done < "$base/modules.txt"
cp "$here"/../graffiti-133-exterior-triangle-transversal/src/*.lean "$src/"
run BicycleTriangleDeletion133
cp "$here"/../graffiti-133-one-exterior-triangle/src/*.lean "$src/"
for m in BicycleTriangleCapsules1133 BicycleTriangleCapsules2133 BicycleTriangleCapsules3133 BicycleExpandedThreeProfiles133 BicycleExpandedFourProfile133 BicycleOneExteriorTriangle133; do
  run "$m"
done
cp "$here"/../graffiti-133-two-exterior-triangles/src/*.lean "$src/"
run BicycleTwoExteriorTriangles133
cp "$here"/../graffiti-133-singleton-seven-general/src/*.lean "$src/"
for m in ExteriorBowtie133 BicycleTripleCrossModel133 BicycleThreeTrianglesCapsulesA133 BicycleThreeTrianglesCapsulesB133 BicycleSingletonSevenGeneral133; do
  run "$m"
done
cp "$here"/../graffiti-133-multiple-contact-small-scopes/src/*.lean "$src/"
run C7MultiSmallScopes133
cp "$here"/../graffiti-133-dominating-c7-radius-four/src/*.lean "$src/"
for m in BicycleExactTriangleCharge133 C7MultiScoreHelpers133 C7MultiWeightedLocal133 C7MultiWeightedGlobal133; do
  run "$m"
done
cp "$here"/../graffiti-133-dominating-c7-path-eight-free/src/*.lean "$src/"
for m in C7MultiP8AdjCharge133 C7MultiProfileCap133 C7MultiP8Mean133; do
  run "$m"
done
for m in C7MultiRadius4Caps133 C7MultiRadiusFourMean133; do run "$m"; done
cp "$here"/../graffiti-133-nested-c7-two-gate/src/*.lean "$src/"
run NestedCoreCritical133
cp "$here"/../graffiti-133-nested-c7-crossing-budget/src/*.lean "$src/"
for m in NestedCoreGateScore133 NestedCoreC7CrossBudget133; do run "$m"; done
cp "$here"/../graffiti-133-nested-c7-three-gate/src/*.lean "$src/"
for m in NestedCoreThreeGate133 NestedCoreThreeGateC7Budget133; do run "$m"; done
for pkg in graffiti-133-c7-core graffiti-133-nested-outer-excess graffiti-133-nested-singleton-leaf-crossings graffiti-133-nested-adjacent-gate graffiti-133-private-cross; do
  cp "$here/../$pkg"/src/*.lean "$src/"
done
for m in C7CoreOrder133 NestedCoreCleanArms133 NestedCoreTwoExcess133 NestedCoreSingletonGate133 NestedCoreAdjacentGate133 NestedCoreLongGateAtlas133 NestedCorePrivateCrossKernel133 NestedCorePrivateCrossRows133 NestedCorePrivateCrossLift133; do
  run "$m"
done
(cd "$here/src" && sha256sum -c ../sources.sha256)
cp "$here"/src/*.lean "$src/"
for m in NestedCoreShortArm133 NestedCoreCleanRemoteScore133 NestedCoreShortCrossingScore133 NestedCoreRadiusFourArchetypes133 NestedCorePrivateGenericKernel133 NestedCorePrivateExpandedSpec133 NestedCorePrivateSingleRows133 NestedCorePrivateDualRows133 NestedCorePrivateExpandedResult133 NestedCorePrivateExpandedFit133 NestedCorePrivateExpandedRealLift133 NestedCorePrivateFullTriangle133 NestedCorePrivatePaidTrim133 NestedCoreLongGateRadius133 NestedCorePrivateUnlimitedCross133 NestedCorePrivateWitnesses133 NestedCorePrivateOrbit133 NestedCoreMinimumTwoCoreUnlimited133; do
  run "$m"
done
