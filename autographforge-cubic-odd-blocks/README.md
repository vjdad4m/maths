# AutoGraphForge: one cubic witness, seventeen additional rows

The [pinned catalogue](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L832-L851) and [its clique-cover cluster](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1160-L1162) list these seventeen statements. This package reuses the graph already formalized for [row 1160](../autographforge-1160/), not a new graph or seventeen independent discoveries.

Subdivide one edge in each of three disjoint copies of K₃,₃ and connect a new hub to the three subdivision vertices. The resulting graph is connected, cubic and triangle-free. Its order is 22, size is 33, annihilation number and harmonic index are both 11, matching number is 10, and both the edge-cover number and vertex clique-cover number are 12.

| Physical line | False comparison on the witness |
| ---: | --- |
| 832 | Vertex clique-cover number ≤ matching number: 12 ≤ 10 |
| 837 | Annihilation = edge-cover number: 11 = 12 |
| 838 | Edge-cover number = matching number: 12 = 10 |
| 839 | Annihilation = matching number: 11 = 10 |
| 840 | Harmonic index = matching number: 11 = 10 |
| 841 | Edge-cover number = harmonic index: 12 = 11 |
| 843 | Vertex clique-cover number ≤ harmonic index: 12 ≤ 11 |
| 844 | Twice the edge-cover number = order: 24 = 22 |
| 845 | Twice the matching number = order: 20 = 22 |
| 846 | Three times the matching number = size: 30 = 33 |
| 847 | Three times the edge-cover number = size: 36 = 33 |
| 848 | Half the order = edge-cover number: 11 = 12 |
| 849 | Half the order = matching number: 11 = 10 |
| 850 | One third the size = matching number: 11 = 10 |
| 851 | One third the size = edge-cover number: 11 = 12 |
| 1161 | Twice the vertex clique-cover number ≤ order: 24 ≤ 22 |
| 1162 | Three times the vertex clique-cover number ≤ size: 36 ≤ 33 |

In particular, 839/840/845/846/849/850 are equivalent in the stated class, as are 837/841/844/847/848/851. Lines 1161/1162 are reformulations of the already resolved 1160 in their stated class. Row 842 concerns a different conjecture and is not included.

Deleting the hub leaves three lobes on seven vertices each. A matching has at most one hub edge and at most three edges internal to each lobe, so its size is at most ten. A matching of ten is explicit; two more hub edges cover the two unmatched subdivision vertices. Conversely, choosing one incident cover edge per vertex gives a complement coloring by the selected edges. Thus the earlier clique-cover lower bound of twelve also bounds every edge cover from below. The harmonic calculation uses the regular-graph identity proved for [row 595](../autographforge-595/).

[Transfer.lean](Transfer.lean) gives the exact invariants and all seventeen failures. Use Lean 4.19.0 and the prepared Mathlib checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From a checkout of this repository run:

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash autographforge-cubic-odd-blocks/replay.sh
```

The replay verifies that the witness theorem and the seventeen refutations use only `propext`, `Classical.choice`, and `Quot.sound`.
