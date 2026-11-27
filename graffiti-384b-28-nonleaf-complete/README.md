# Graffiti.pc #384b for 29 triangle-count types and 28 nonleaves

For every finite simple graph $G$ with 29 distinct vertex triangle counts and exactly 28 vertices of degree at least two, the two-domination number satisfies **γ₂(G) ≤ |V(G)| − 15**. Zero counts as a type whenever some vertex realizes it. A two-dominating set contains at least two neighbors of every vertex outside the set. The theorem applies to disconnected graphs as well. Together with the earlier quota reduction it proves that a counterexample at diversity 29 must have either 29 or 30 nonleaves. Those two possibilities and the general conjecture remain outside this result. [Original-graph theorem and residual alternatives](FinishNonleaves28.lean)

## Proof

Suppose a graph with these parameters violates the bound. The frozen reductions give a 28-vertex core with distinct positive triangle counts and two-domination number at least 14. The frozen five-clique-free theorem forces a five-clique in this core. The earlier pivot argument supplies two cubic vertices with triangle counts two and three. Let their open neighborhoods be U and L. Every five-clique contains at least three vertices of U ∪ L, and U and L share at most one vertex. The cubic vertices cannot be adjacent, since adjacency would give them at least two common neighbors. [Frozen predecessor sources](https://github.com/vjdad4m/maths/tree/83846039811e7190d45f65e2e6fccba22573ffd3/graffiti-384b-28-five-free)

**One common neighbor.** Retain the common neighbor, one private neighbor of each cubic, and eight of the 21 exterior vertices. An exterior vertex with at most two contacts in U ∪ L has a four-clique-free neighborhood, since a four-clique there would extend to a five-clique violating the three-contact condition. For larger contact counts, the elementary triangle-count bound suffices. Across all four choices of private neighbors, the rank bounds permit at most 2,433,041 repairs. If each eleven-vertex sample needed at least three repairs, the total would be at least 2,441,880. [Neighborhood bound](FiveCommonGeometry28.lean) · [Sampling and comparison](FiveCommonSaving28.lean)

**Disjoint neighborhoods.** Sample from the 20 vertices outside the two cubics and their six neighbors. Each choice in the table retains eleven vertices. Add every omitted vertex with fewer than two retained neighbors to get a two-dominating set.

| Fixed vertices | Exterior sample size | Choices of fixed vertices | Weight |
|---|---:|---:|---:|
| Two vertices of U and two of L | 7 | 9 | 3 |
| The first cubic and two vertices of L | 8 | 3 | 2 |
| The second cubic and two vertices of U | 8 | 3 | 2 |

Across these trials the two cubics never need repair. The other 26 vertices have distinct positive triangle counts excluding two and three. Each exterior vertex receives a bound on its weighted repair count that depends on the rank of its triangle count. At each of the six neighbors of the cubics, the same rank bound can be decreased by 95,238, using one guaranteed neighbor within its own triple. The rank bounds total 11,198,043 before the six decreases. The resulting upper bound of **10,626,615** is below the **10,814,040** required if every sample needed at least three repairs. Thus one sample extends to a two-dominating set of size at most 13, contradicting the core reduction. [Rank and rotation table](SixRows28.lean) · [Full counting argument](DisjointFinish28.lean)

## Source and replay map

| Module | Role |
|---|---|
| FiveCommonGeometry28, FiveCommonSaving28 | Extend the 28-vertex one-common-neighbor proof to the three-contact condition |
| SixGeometry28, RankBoard28 | Prove degree and triangle-count bounds and assign all 26 ranks |
| SixRows28, MixedTrials28 | Verify the finite integer bounds and derive sample counts for each vertex |
| BoardBudget28, DisjointFinish28 | Prove the necessary repair total and the disjoint-neighborhood contradiction |
| FinishNonleaves28 | Combine the cases in the original graph and prove the remaining quota alternatives |

The package reuses the invariant definitions, the original-graph reduction in Core28.original_clique, and the five-clique-free theorem in Sparse28.five_clique_required. PortRepair28 and PortSaving28 supply the shared-neighbor repair construction and rank budget. The earlier 30-vertex one-common-neighbor and disjoint-neighborhood arguments supplied geometry and ranking patterns. Their graph orders and sample sizes differ, so the disjoint-neighborhood budget here is proved anew. An exploratory integer calculation suggested the weights. Lean checks every admissible parameter combination and proves that they cover every graph in the stated class. [Public checked-result index](https://github.com/vjdad4m/maths/blob/main/README.md)

Two recorded runs used independent empty build directories. Each authenticated 309 predecessor source and object hashes, compiled all nine new modules with warnings as errors, matched nine output hashes, and verified 15 axiom reports against the allowlist of propext, Classical.choice, and Quot.sound. The runner scans all 318 project sources for proof placeholders, custom axiom declarations, and native_decide. The toolchain is Lean 4.19.0 at 6caaee842e94 and Mathlib v4.19.0 at c44e0c8ee63ca166450922a373c7409c5d26b00b. [First replay](StrictFull.first.log) · [Second replay](StrictFull.log) · [New source hashes](NEW-SOURCES.sha256) · [New object hashes](NEW-OBJECTS.sha256) · [Predecessor source hashes](PRIOR-SOURCES.sha256) · [Predecessor object paths and hashes](CHECKED-OBJECTS.tsv)

Run the entry point from the unpacked package. Set CROSSFOUR_LEAN_BIN and CROSSFOUR_MATHLIB to your Lean binary directory and matching Mathlib checkout if needed. The recorded runs used the first command. The second command rebuilds the predecessors from the bundled sources. [Replay entry point](replay.py)

~~~sh
python3 replay.py --checked /absolute/path/to/shared/workspace
python3 replay.py --cold
~~~
