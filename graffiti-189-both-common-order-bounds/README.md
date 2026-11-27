# Graffiti.pc #189: order bounds for shared attachments on both sides

Consider a distance-two cut pair whose deletion leaves exactly two connected components. An attachment is a vertex adjacent to at least one vertex of the cut pair, and each component has a vertex adjacent to both cut vertices. Assume the degree-five even-distance bound and connectivity after any single vertex deletion.

* With at least four attachments on each side, the graph has at most 16 vertices. [Order bound](src/DegreeFiveBothAtLeastFour189.lean)
* If either side has exactly four attachments, the graph has at most 15 vertices. [Order bound](src/DegreeFiveBothNonsaturated189.lean)
* If both have exactly four attachments, the graph has at most 14 vertices. [Order bound](src/DegreeFiveBothFourteen189.lean)

These conclusions are structural and do not use the degree-pair premise. They do not assert traceability in the residual profiles. The counting uses the distance-two shells of the two cut vertices. In tight cases, the visibility lemmas rule out hiding vertices on one side from a cut vertex's distance-two shell. [Pure-side visibility](src/DegreeFivePureShoreVisible189.lean) · [One-color visibility](src/DegreeFiveOneColorVisible189.lean)

## Replay

Use Lean 4.19.0 and Mathlib 4.19.0 at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Build the [five-attachment geometry](../graffiti-189-both-five-shores/) and [balanced common-neighbor infrastructure](../graffiti-189-balanced-three-four/) and keep their objects and pinned Mathlib on the Lean search path. Then run:

```sh
set -e
sha256sum -c sources.sha256
mkdir -p build
export LEAN_PATH="$PWD/build:${LEAN_PATH:-}"
while read -r module; do
  lean -j1 -s 65536 -DElab.async=false -DwarningAsError=true -o "build/$module.olean" "src/$module.lean"
done < modules.txt
```

The checks of the listed sources passed with warnings as errors and only `propext`, `Classical.choice`, and `Quot.sound` in the public axiom reports.
