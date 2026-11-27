# AutoGraphForge line 5170

**Disproved.** A connected 10-regular bipartite graph on 38 vertices has edge cover number 19 and minimum edge-domination size 10, so the claimed lower bound fails (10 < 71/7).

[Exact upstream statement](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L5170). The record was marked proposed, not a claim of historical priority.

## Connected family

For each d ≥ 2, take two disjoint copies of K(d,d−1) and add a perfect matching between their larger parts. The public row 1957 development proves that the resulting graph is connected and d-regular on 4d−2 vertices, and gives the exact vertex clique cover size 2d−1 and minimum maximal matching size d. Each joining edge is disjoint from the others and the joining edges dominate the graph’s edges. Swapping the bipartition on one copy makes the whole graph bipartite. [Published family and exact matching proof](https://github.com/vjdad4m/maths/blob/5314608a20cb06f1f0ac3edc32f8e0da51417622/autographforge-1957/Twin.lean)

We transfer the family’s clique-cover formula to the edge-cover optimizer. In every isolate-free, triangle-free graph the largest clique has size at most two. Each 2-vertex clique provides its edge and each singleton extends to an incident edge. Conversely an edge cover gives a clique partition by assigning each vertex to an incident covering edge. `Family.lean` proves equality of the two optimizers using their original definitions. Thus ρ = 2d−1 and γₑ = d. On this family, the antecedent of 5170 reduces to d > 9. Every d ≥ 10 refutes it. For every rational c < 2 and fixed rational A some member also satisfies ρ > cγₑ + A. The family and the matching construction are credited to the row 1957 development. The contribution here is the checked edge-cover transfer and its exact application to these CEGIS rows. [Prior row 1957 analysis and attribution](https://github.com/vjdad4m/maths/tree/5314608a20cb06f1f0ac3edc32f8e0da51417622/autographforge-1957)

## Replay

In Lean 4.19.0 with built Mathlib 4.19.0, run `MATHLIB_DIR=/path/to/mathlib4 bash replay.sh`. [Strict replay](Replay.log).
