# AutoGraphForge row 33: burning number versus Slater number

**Disproved.** The [normalized conjecture](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L33) says that the burning number of a nontrivial connected graph is at most its Slater number plus one. Join a clique on eight vertices to an eight-vertex path by a single edge. The graph has burning number 4 and Slater number 2, so the proposed bound is 3.

The [Lean proof](Lollipop.lean) also shows that the gap is unbounded: the same family keeps Slater number 2 as both parts grow. The number of distinct heights that k fires can cover is at most k². Lean checks the exact finite witness and the family.

In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/autographforge-33/replay.sh`. See the [Lean replay log](Replay.log) and [independent GraphCalc output](SourceReplay.log). The independent [source checker](check-source.py) uses the pinned AutoGraphForge source above and GraphCalc commit `ce66ac7390d945885e33f372e29c896fa32e9bc4` with NetworkX, PuLP, and PySCIPOpt.
