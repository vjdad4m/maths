# AutoGraphForge row 500: outer-connected domination of cographs

**Proved in Lean.** For every connected cograph of order at least two,
an outer-connected dominating set exists and its minimum size is at most
the independence number. [Pinned physical row 500](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L500).

The proof combines the [proper join lemma from row 534](../autographforge-534/)
with the [outer-connected domination definition from row 370](../autographforge-370/).
If the independence number is one, the graph is complete and a singleton
works. If a universal vertex exists and the independence number is at least
two, a maximum independent set dominates and omits that vertex, which
connects its complement. Otherwise each side of the proper join has
at least two vertices. Selecting one from each side dominates the graph
and leaves a nonempty join on the complement. That pair has size two,
at most the independence number.

The final theorem quantifies over all finite graphs under the stated
hypotheses, not just graphs already carrying a numerical result. It proves
that the optional GraphCalc-style optimum exists and satisfies the bound.
The exact row was absent from the inspected upstream refutation and released
Lean files. This establishes the pinned catalogue result, not first priority.

Replay with Lean 4.19.0 and built Mathlib revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b`:
`MATHLIB_DIR=/path/to/mathlib4 bash replay.sh`.
