# AutoGraphForge 2535: the additive allowance of two fails

**Disproved in Lean.** The [pinned statement](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2535), generated ID `9ea0ea74`, asserts that the two-forcing number is at most the Havel–Hakimi residue plus two in every nontrivial connected planar graph.

Take a chain of three copies of K₂,₆, joining successive copies by bridges at their hubs. Use different hubs for the two bridges in the middle copy. This extends the [two-fan obstruction for row 842](../autographforge-842/).

- **Two-forcing number 12.** If three vertices on the six-vertex side of a copy start uncolored, neither of their two common neighbors can make the first force into that triple. Thus every forcing set must contain at least four vertices on each six-vertex side. Four on each side suffice: first color the hubs, then the remaining two on each six-vertex side.
- **Residue 8.** The degree list has four 7s, two 6s, and eighteen 2s. The first eight Havel–Hakimi steps leave sixteen 1s. The final eight steps leave eight 0s.
- **Connected and planar.** The bridges connect the three copies. A straight-line drawing places each copy in a separate strip. An integer determinant certificate checks that no vertex lies in the interior of an edge and that distinct edge interiors do not intersect.

Hence 12 > 8 + 2. [Witness2535.lean](Witness2535.lean) proves the invariants and connectivity; [Plane2535.lean](Plane2535.lean) proves planarity and the literal catalogue negation.

The pinned release marked the row proposed with no Lean proof. Its exact statement and ID were absent from the inspected upstream refutations and released Lean proof files. For conventions, see the pinned [GraphCalc forcing rule](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/zero_forcing.py#L156-L195) and [residue implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/degree.py#L620-L688).

## Replay

Use Lean 4.19.0 and built Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash autographforge-2535/replay.sh
```

Replay compiles from source with warnings as errors and verifies only `propext`, `Classical.choice`, and `Quot.sound`.
