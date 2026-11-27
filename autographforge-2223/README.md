# AutoGraphForge normalized line 2223

**Disproved in Lean.** The [pinned row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2223)
(ID `00da7483`) asserts that a nontrivial K₄-free graph has triameter
at most four times its sub-total domination number plus four.

Start with a path labeled 0 through 6. Add a second leaf at vertex 1 and
three more vertices adjacent precisely to 1 and 3. This connected bipartite
graph has **triameter 14** and **sub-total domination number 2**; the proposed
bound is 12. The three leaves have pairwise distances 2, 6 and 6, and the
two largest degrees 6 and 5 reach order 11.

The Lean proof checks the graph hypotheses, its distance table, the
triameter and the sub-total domination number. An optional GraphCalc
comparison is in `check_source.py`.

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`,
then run `MATHLIB_DIR=/path/to/mathlib4 bash autographforge-2223/replay.sh`.
