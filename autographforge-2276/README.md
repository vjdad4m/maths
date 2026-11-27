# AutoGraphForge normalized line 2276

**Proved in Lean, with equality at the 17-vertex cycle.** Every nontrivial
Eulerian subcubic graph satisfies `burning_number ≤ slater / 3 + 3`.
This is a formalized corollary of the known cycle burning bound, not a claim
of new priority. The exact
[catalogue row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2276)
is pinned.

The [GraphCalc Eulerian predicate](https://graphcalc.readthedocs.io/en/latest/_modules/graphcalc/graphs/core/basics.html)
uses connectedness and even degrees. Subcubicity therefore gives maximum
degree two, and the same spanning-path construction used for
[normalized line 2055](../autographforge-2055/) yields the bound
with the new budget. The [path and cycle burning results](https://arxiv.org/abs/1507.06524)
are due to Bonato, Janssen and Roshanbin.

See `TraceableBurn.row2276_rat` in `src/Row2276.lean` and
`PathCycleSharpness.row2276_equality` in `src/C17.lean`.
Run `bash autographforge-2276/replay.sh` with Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
