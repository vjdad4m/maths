# AutoGraphForge normalized line 2598

**Disproved in Lean.** The [pinned row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2598)
(ID `a0a6bf25`) bounds average shortest path length by two thirds of
the harmonic index plus one half for nontrivial subcubic graphs.

The witness is a path labeled 0 through 8 with one extra leaf attached
to vertex 1 and another to vertex 7. This 11-vertex, maximum-degree-three
tree has harmonic index **24/5** and mean distance **204/55**. The proposed
bound is **37/10**, smaller by **1/110**.

`DoubleBroom2598.row2598_false` checks the exact disproof, including the
graph and both invariant values. No claim of order-minimality is needed.

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`,
then run `MATHLIB_DIR=/path/to/mathlib4 bash autographforge-2598/replay.sh`.
