# Graffiti.pc #384b: the upper triangle-skeleton case at diversity eleven

Let G be a finite simple graph with eleven distinct vertex triangle-count
types. Let its triangle skeleton retain just the edges that belong to a
triangle. If the skeleton has ten vertices of degree at least three, then
G has a two-dominating set of size at most its order minus six.

This also settles the entire diversity-eleven case in which triangle count
one is not realized. No connectivity assumption is needed. The residual
diversity-eleven graphs with score one are not settled by this package.

Main results: `Graffiti384b.DiversityEleven.exact_upper_ten` and
`Graffiti384b.DiversityEleven.exact_of_no_score_one`, in
[UpperTenExact384b.lean](src/UpperTenExact384b.lean).

## Proof

The fixed-cubic result from the upper-palette analysis shows that a
counterexample has ten nonisolated skeletal vertices with distinct scores,
exactly two nonadjacent cubics of scores two and three, and a balanced
maximum cut. Every noncubic has degree and score at least four and at
least three neighbors across this cut. Any vertex with two same-side
neighbors is adjacent across the cut to one of the two critical cubics.

Relabeling the two cubic neighborhoods gives four motifs. A separate
finite proof of motif symmetry reduces balanced cuts to nineteen
profiles. The graph-to-mask adapter transports the necessary cut
conditions exactly. The nineteen checked trees contain 393 leaves total,
at most 70 in one profile. Each decisive leaf either proves a degree,
score, or cut condition impossible or explicitly retains four vertices
giving the other six two neighbors. Restoring all vertices outside
the ten-vertex board preserves the six omissions.

No external numerical solver is used in replay. The numeric trees use
ordinary Lean `decide` and a separately proved soundness theorem.
The strict axiom audit allows only `propext`, `Classical.choice`, and
`Quot.sound`.

## Replay

Use Lean 4.19.0 (6caaee842e94) and Mathlib v4.19.0
(c44e0c8ee63ca166450922a373c7409c5d26b00b). Build the earlier even-palette,
upper-cubics, diversity-eleven-structure, eight-nonleaves, and
ten-nonleaves proof modules with their documented transitive
prerequisites. Place those object directories and the pinned Mathlib
objects on `LEAN_PATH`, then run `lake env bash /path/to/this/package/replay.sh`.
