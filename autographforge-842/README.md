# AutoGraphForge 842: a 14-vertex connected counterexample

**Disproved in Lean.** The [pinned statement](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L842), generated ID `687f3719`, asserts that the two-forcing number is at most the Havel–Hakimi residue in every nontrivial triangle-free planar graph.

Take two copies of K₂,₅ and join one hub from each copy by a bridge. The graph is connected, bipartite, and has a straight-line plane drawing. It has two groups of five degree-two vertices.

- **Two-forcing number 6.** If a group starts with at most two colored vertices, at least three of its vertices remain uncolored. They have the same two neighbors; both neighbors have too many uncolored neighbors to make the first force into those three. Thus every forcing set needs three vertices from each group. Conversely, three from each group color the four hubs on the first round and the remaining four vertices on the next.
- **Residue 5.** The degree sequence is 6, 6, 5, 5, and ten 2s. The first four Havel–Hakimi steps leave ten 1s; five more steps leave five 0s. This uses the same algorithm as [Graffiti.pc #324](../graffiti-324/Proof324.lean).

[Witness842.lean](Witness842.lean) proves the exact invariants, connectivity and triangle-freeness, using the [existing forcing dynamics](../autographforge-star/StarCone.lean). [Plane842.lean](Plane842.lean) proves planarity with embedded straight-line segments and establishes the negated catalogue statement. Its determinant method comes from [AutoGraphForge 303 and 1908](../autographforge-303/AutoGraphForgePlanar.lean).

The pinned release marked the row proposed, with no recorded Lean proof. The exact statement and ID were absent from the inspected refutation and Lean proof files. The [pinned GraphCalc forcing rule](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/zero_forcing.py#L156-L195) uses simultaneous rounds; the [pinned residue implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/degree.py#L620-L688) uses the descending reranking algorithm. The argument does not rely on the catalogue allowing disconnected graphs.

## Replay

Use Lean 4.19.0 and built Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash autographforge-842/replay.sh
```

The replay checks the proof from source with warnings as errors and only `propext`, `Classical.choice`, and `Quot.sound`.
