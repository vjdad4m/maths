# AutoGraphForge row 242: the three-rainbow number equals graph order

**Proved in Lean**, using the singleton-color convention.

Every neighborhood is independent because the graph is triangle-free. Claw-freeness then caps each degree at two. An uncolored vertex would need three distinct neighbors, one per nonzero color. Thus all feasible labelings color every vertex. The exact theorem does not need the catalogue's nontriviality condition.

[Pinned catalogue entry](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L242)

```text
[   412] (((nontrivial) ∧ (claw_free)) ∧ (triangle_free)) ⇒ order ≤ three_rainbow_domination_number    -- promising:class
```

The theorem is `TriangleFreeRainbow242.row242`. This is a Lean proof of the
pinned row, not a claim about first discovery.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
From the repository root, run `bash autographforge-242/replay.sh`.
