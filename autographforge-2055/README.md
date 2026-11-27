# AutoGraphForge normalized line 2055

**Proved in Lean, with equality at the 10-vertex path.** Every nontrivial
claw-free tree satisfies `burning_number ≤ slater / 2 + 2`. This is a
formalized corollary of the known path burning bound, not a claim of new
priority. The exact
[catalogue row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2055)
is pinned.

An acyclic graph's neighbors at a vertex are pairwise nonadjacent, so
claw-freeness gives maximum degree two. The earlier #183 classification
supplies a spanning path, and sorted degrees give `n ≤ 3 * slater`.
Label the path intervals between successive squares; a radius-`j` ball
covers the interval of at most `2j+1` vertices. The resulting burning
schedule fits the stated budget. The [path and cycle burning results](https://arxiv.org/abs/1507.06524)
are due to Bonato, Janssen and Roshanbin. The predicates match
[GraphCalc’s covering model](https://graphcalc.readthedocs.io/en/latest/_modules/graphcalc/graphs/invariants/zero_forcing.html).

See `TraceableBurn.row2055_rat` in `src/Row2055.lean` and
`PathCycleSharpness.row2055_equality` in `src/P10.lean`.
Run `bash autographforge-2055/replay.sh` with Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
