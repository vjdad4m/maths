# AutoGraphForge normalized line 2039

**Disproved in Lean.** The [pinned row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2039)
(ID `c6657d7f`) gives `diameter ≤ (43 * slater + 4) / 15` in the stated
claw-free and K₄-free class.

Start with a path labeled 0 through 9. Add the four edges between vertices
two labels apart on 0 through 5. The resulting graph is connected, claw-free,
and K₄-free. It has **diameter 7** and **Slater number 2**, whereas the proposed
upper bound is 6. The graph is connected, so conventions for diameter on
disconnected graphs do not matter.

The exact graph properties, metric, and Slater number are checked in
`SquaredPath.lean`. The optional source and GraphCalc checks are in
`check_source.py`.

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`,
then run `MATHLIB_DIR=/path/to/mathlib4 bash autographforge-2039/replay.sh`.
