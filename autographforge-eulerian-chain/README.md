# AutoGraphForge: two failed Slater-number bounds on Eulerian chordal graphs

Use a chain of five cliques of orders 3, 3, 5, 3 and 3. Consecutive cliques share one vertex, with distinct attachment vertices within each interior clique. The result has 13 vertices, is connected and chordal, and has even degree at every vertex.

The two largest degrees are 6 and 6. One vertex contributes at most 7 to the Slater test, whereas two contribute 14, so the Slater number is 2. The exact radius is 3. The triameter, the largest sum of the three pairwise distances among three distinct vertices, is 11; a maximizing triple has distances 1, 5 and 5.

| Pinned normalized row | Claimed bound | Violation |
|---|---|---|
| [501](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L501) | radius ≤ Slater number | 3 > 2 |
| [764](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L764) | triameter ≤ 4 × Slater number + 2 | 11 > 10 |

Both rows impose nontriviality, chordality, and the Eulerian property. [The Lean certificate](Chain.lean) verifies all three hypotheses and the exact invariant values. It reuses the elimination-order and distance-table arguments from the [book-tail certificate](../autographforge-book-tail/README.md). For each distance table the checker constructs a walk realizing the entry and proves no shorter walk exists. On this connected witness there is no ambiguity about the values assigned to disconnected graphs.

Run `lake env lean -DwarningAsError=true /path/to/maths/autographforge-eulerian-chain/Chain.lean` in a Lean and Mathlib 4.19.0 project. The checker reports only `propext`, `Classical.choice`, and `Quot.sound`.
