# AutoGraphForge row 1813: vertex cover versus harmonic index

**Disproved in Lean.** [Pinned physical row 1813](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1813)
proposes vertex cover at most 35/18 times harmonic index. In a clique of
order n a vertex cover omits at most one vertex, and omitting one works.
The [regular-graph harmonic identity from row 595](../autographforge-595/)
gives harmonic index n/2. Lean verifies that every clique with n ≥ 37
violates the bound. The witness K₃₇ has vertex cover 36, versus a
proposed upper bound of 1295/36.

The literal row was absent from the inspected upstream refutation and
released Lean files. This is a direct reuse of the regular harmonic
identity, not a claim of historical priority.

Replay with Lean 4.19.0 and a built Mathlib checkout:
`MATHLIB_DIR=/path/to/mathlib4 bash replay.sh`.
