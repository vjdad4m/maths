# AutoGraphForge: cubic clique-cover implications

Two more physical lines of the pinned catalogue are false.

| Line | Stable ID | Hypothesis of the false implication on a cubic graph |
|---|---|---|
| [3232](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L3232) | `8b43f6e3` | Size divided by three is strictly less than the vertex clique-cover number. |
| [4862](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L4862) | `d10d9a89` | The harmonic index is strictly less than the vertex clique-cover number. |

The existing [22-vertex witness](../autographforge-cubic-odd-blocks/) has 33 edges, harmonic index 11 and vertex clique-cover number 12. Both proposed hypotheses are true, but the graph is cubic. The comparisons agree for every cubic graph, by the [regular harmonic identity](../autographforge-595/). These are two catalogue certificates reusing one obstruction, not independent discoveries. Row 4862 is the contrapositive form of the already certified row 843 on nontrivial graphs.

The pinned release labels both exact IDs `proposed`, with no Lean proof or recorded counterexample. Neither ID was found in the release's three refutation files or its released Lean proof files. This is an explicit certification of two catalogue entries, not a priority claim.

Replay [OddImplications.lean](OddImplications.lean) using Lean 4.19.0 and a built Mathlib checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`:

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash autographforge-cubic-odd-implications/replay.sh
```

Both theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
