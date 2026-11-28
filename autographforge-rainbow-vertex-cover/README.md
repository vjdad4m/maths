# AutoGraphForge: singleton rainbow domination bounds vertex cover

**Proved in Lean:** [row 645](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L645) (`399b9c94`) and [row 671](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L671) (`c66a3fde`). Both compare vertex cover with singleton three-rainbow domination; the former assumes connectedness and the latter assumes regularity. The proof needs neither.

## General theorem

For any positive palette size k, a finite simple graph of maximum degree at most k has vertex-cover number at most its singleton k-rainbow domination number.

Each uncolored vertex must see all k colors. A neighbor carries at most one color, so there must be k distinct colored neighbors. The degree bound leaves no room for an uncolored neighbor. Thus every edge has a colored endpoint, and the colored vertices form a vertex cover. Minimize over feasible labelings. The local lemma only needs the degree bound at the uncolored vertices, not at the colored ones.

This reuses the [definitions and distinct-neighbor argument from row 1121](../autographforge-1121/HallRainbow.lean), but does not need Hall's theorem: we need a vertex cover, not a partition into cliques. In particular the conclusion is not a restatement of row 1121, since the two cover numbers need not agree. The singleton-label convention is essential to the argument; allowing a vertex to carry a set of colors changes it. The pinned release records both statuses as proposed with no Lean proof; the two IDs are absent from the inspected refutation and verified-proof files. No novelty claim is made for the underlying counting argument.

## Replay

Use Lean 4.19.0 and a built Mathlib checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Build `Mathlib.Combinatorics.Hall.Finite` first if it is missing from a partial Mathlib cache.

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash autographforge-rainbow-vertex-cover/replay.sh
```

[RainbowVertexCover.lean](RainbowVertexCover.lean) checks the local lemma, the general bound, and the specialization to both catalogue entries. All four exported declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
