# AutoGraphForge normalized line 362

**Disproved in Lean.** The [pinned row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L362)
(ID `1be64126`) says that a nontrivial triangle-free graph has burning number
at most three halves of its sub-total domination number.

Start with a path labeled 0 through 9 and add seven vertices, each adjacent
only to 0 and 2. This connected bipartite graph has burning number **4** and
sub-total domination number **2**, so the claimed upper bound is **3**.
Three rounds cover at most nine of the ten path vertices, while the sources
0, 4, 7, 9 burn the whole graph in four rounds. The two largest degrees,
9 and 8, sum to the order 17.

See `BicliqueTail362.row362_false` in `BicliqueTail.lean`. Its checked
graph, metric, and parameter values use only standard Lean axioms.
The optional `check_source.py` compares the witness against GraphCalc;
`audit_release.py` records the pinned catalogue and search scope.

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`,
then run `MATHLIB_DIR=/path/to/mathlib4 bash autographforge-362/replay.sh`.
