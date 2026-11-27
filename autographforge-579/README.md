# AutoGraphForge row 579: independence is bounded by the two-rainbow number

**Proved in Lean**, using the singleton-color convention.

Compare an independent set with the colored set. Each uncolored independent vertex needs two distinctly colored neighbors outside the independent set. By claw-freeness, each colored vertex outside the independent set sees at most two independent vertices. Counting the same incidences gives the bound. This proof does not need the catalogue's bipartite or nontriviality conditions.

[Pinned catalogue entry](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L579)

```text
[   160] (((nontrivial) ∧ (bipartite)) ∧ (claw_free)) ⇒ independence_number ≤ two_rainbow_domination_number    -- promising:class
```

The theorem is `RainbowIndependent579.row579`. This is a Lean proof of the
pinned row, not a claim about first discovery.

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` on `LEAN_PATH`.
From the repository root, run `bash autographforge-579/replay.sh`.
