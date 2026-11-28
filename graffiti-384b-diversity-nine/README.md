# Graffiti.pc #384b: all finite graphs with exactly nine triangle-count types

For every finite simple graph with exactly nine distinct vertex triangle-counts,
there is a two-dominating set of size at most the order minus five. This is the
exact #384b bound at diversity nine. Connectedness is not required, and a zero
triangle count is included when present. This does not settle unrestricted
odd diversity.

Main theorem: `Graffiti384b.DiversityNine.exact_of_nine_types` in
[DiversityNineExact384b.lean](src/DiversityNineExact384b.lean).

## Proof outline

Let q count the vertices of degree at least two. All triangles lie in their
induced core, while other vertices contribute only score zero. Thus q≥8.
The earlier q8, q9, and q10 theorems handle those three cases. The general
bound omitting at least the ceiling of q/3 vertices handles q≥13.
Only q=11 and q=12 remain.

There are at least eight distinct positive core triangle counts. Pick
representatives of the two largest distinct scores. Each is at least
seven, so both anchors have degree at least five. If they have at least
five common neighbors, omit five of those neighbors. Otherwise relabeling
by anchor contact gives 46 possible shapes at q=11 and 69 at q=12.

Each shape fixes the edges on the two anchors. An explicit Boolean
decision tree covers all assignments of the remaining edge bits. Leaf
checks either prove that the anchor or score-palette conditions fail or
produce a retained set of at most q−5 vertices. Every omitted vertex
either has two forced neighbors in that retained set or has no possible
omitted neighbor. In the second case, all its actual ambient neighbors are
retained and its ambient degree is at least two.

The bitproofs are Lean declarations, admitted by a generic checked
soundness theorem and ordinary `decide`. No external numerical solver,
`native_decide`, additional axiom, or unchecked oracle is used.

## Replay

Use Lean 4.19.0 (6caaee842e94) and Mathlib v4.19.0
(c44e0c8ee63ca166450922a373c7409c5d26b00b). Build the baseline,
diversity-29, eight-nonleaf, nine-nonleaf, and ten-nonleaf bundles first.
Leave their compiled objects and transitive Mathlib dependencies on
`LEAN_PATH`. Run `lake env bash /path/to/this/package/replay.sh`.
The proof-shape modules may be replayed in several independent lanes,
provided each shape's Part modules are checked before that shape's final
module. The bundled script uses a sequential replay by default.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
