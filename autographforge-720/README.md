# AutoGraphForge normalized line 720

**Proved in Lean, with equality on K₂.** For a finite claw-free graph with
an edge, the singleton three-rainbow domination number is at least the
independence number plus one. This covers the exact connected domain of the
[pinned row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L720)
(ID `f6e3f6c0`). Each colored vertex has a single color.

Let `I` be a maximum independent set and `B` the colored vertices. Each
vertex of `I \ B` sees three distinct colored neighbors outside `I`.
Claw-freeness means a colored vertex outside `I` sees at most two of them.
Counting these incidences gives `3|I \ B| ≤ 2|B \ I|`, strict enough
unless all of `I` is colored. In that case equality would mean `B = I`;
an edge guarantees some vertex outside `I`, which cannot see all three
colors in an independent neighborhood without yielding a claw.

The proof, graph predicates and sharpness are in `ClawRainbow.lean`.
Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`,
then run `MATHLIB_DIR=/path/to/mathlib4 bash autographforge-720/replay.sh`.
