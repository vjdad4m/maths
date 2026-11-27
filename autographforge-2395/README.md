# AutoGraphForge normalized row 2395

**Disproved in Lean.** The witness is C43. This is a Lean
formalization of a counterexample to the exact pinned row, not a claim
that the upstream release lacked an implicit witness: the released C47 graph,
published for a different statement under `65eacf19`, also violates
this inequality.

[Exact pinned row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2395)

```text
[     5] (((nontrivial) ∧ (planar)) ∧ (subcubic)) ⇒ outer_connected_domination_number ≤ (((3/2) · total_domination_number) + 2)    -- promising:class
```

Replay `MATHLIB_DIR=/absolute/path/to/mathlib4 bash
autographforge-2395/replay.sh` from the repository root with Lean 4.19.0
and Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
The common cycle lemmas live in [row 1130’s package](../autographforge-1130/).
