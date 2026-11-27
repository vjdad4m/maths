# AutoGraphForge normalized line 2473

**Disproved in Lean.** The [pinned row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2473)
(ID `27d9e7c4`) bounds average shortest path length by `(7/5) * slater`
for nontrivial K₄-free, claw-free graphs.

The connected 10-vertex graph used for [row 2039](../autographforge-2039/)
has Slater number 2. Lean checks the total distance 256 over its 90 ordered
pairs of distinct vertices. The mean is **128/45**, greater than the
proposed **14/5** by **2/45**.

The exact result is `MeanDistance2473.row2473_false` in
`MeanDistance.lean`. The graph and distance formula are reused from row 2039.
Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`,
then run `MATHLIB_DIR=/path/to/mathlib4 bash autographforge-2473/replay.sh`.
