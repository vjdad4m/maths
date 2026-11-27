# AutoGraphForge row 583

**Proved, with equality at every positive minimum maximal matching size.** Ján Pastorek's normalized physical row 583 states that every nontrivial K₄-free Eulerian graph has Slater number at most its minimum maximal matching number. Its catalogue ID is `d7f95ad0` and it has 160 touches. The argument proves a stronger statement for every finite simple graph G of minimum degree at least two and every edge-dominating set D in G. Namely, sl(G) ≤ |D|. [Pinned row 583](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L583)

## Proof

Let T consist of all endpoints of the edges in D, and set k = |D|. Then |T| ≤ 2k. Every edge meets T, so a vertex outside T has all its neighbors in T, including at least two distinct vertices. A vertex in T sees itself and the other end of a selected edge. Thus every closed neighborhood meets T at least twice. Counting incidences gives

```text
2 |V(G)| ≤ ∑_{v ∈ T} (deg(v) + 1).
```

Split T into two subsets of size at most k. Each subset contributes at most k plus the sum of the k largest degrees, so this quantity is at least |V(G)|. That is precisely the Slater prefix condition at k. Choosing a minimum edge-dominating set proves sl(G) ≤ γ(L(G)), where L(G) is the line graph. Every maximal matching is also edge dominating. In a connected graph of order at least two, even degrees imply minimum degree at least two. This gives the exact row and dispenses with the K₄-free assumption.

In `Row583.lean`, `of_double_cover` proves the counting step for any vertex set meeting every closed neighborhood at least twice. The intermediate result `of_edge_dominating` allows selected edges to have common endpoints. The final theorem `row583` proves the inequality both for the GraphCalc implementation and for the actual minimum size of an inclusion-maximal matching. On P₄ the middle edge dominates every edge, whereas the largest closed-neighborhood capacity is three. Its Slater number is two. The minimum-degree threshold in the generalization is therefore sharp. See `Boundary.lean`.

## Equality and separation from vertex domination

For each k ≥ 2, `Sharp.lean` establishes the following three values on the connected triangle-free Eulerian family from row 574.

| Invariant | Value |
| --- | ---: |
| Slater number | k |
| Edge domination number and minimum maximal matching size | k |
| Vertex domination number | 2k−1 |

There are k disjoint core edges. Each ordered pair of core vertices belonging to different edges gets 2k new common neighbors of degree two. An additional degree-two connector from one endpoint of pair i to the opposite endpoint of pair i+1 modulo k makes every core degree even. The k core edges form a maximal matching and any edge can dominate at most one of them. Row 574 proves that a set of fewer than 2k−1 vertices fails to dominate. If it omits cores from different pairs, it cannot select all 2k of their common neighbors. Otherwise it consists of the cores outside one omitted pair, leaving that pair undominated.

Write C = 3 + 8k(k−1). The graph has exactly kC vertices. For a core, list its mate, its extra connector, and at most 2·2(k−1)·2k block connectors, according to the order of the pair, the other core, and the copy index. This bounds every closed-neighborhood size by C. Hence any feasible Slater prefix has length at least k. The row theorem gives the reverse inequality. In particular the row 574 family attains equality in row 583 while vertex domination exceeds the Slater number by an unbounded amount. The triangle supplies k = 1. Historical minimality of the examples is outside these results.

## Definitions, release audit and prior work

GraphCalc 2.0.0 calls `sub_k_domination_number(G, 1)`: it sorts degrees decreasingly and takes the first index i for which i plus the sum of exactly the first i entries reaches the order. Its matching wrapper calls `domination_number(nx.line_graph(G))`. The class predicates use order ≥ 2, exclusion of a 4-clique, and NetworkX's connected even-degree Eulerian criterion for undirected graphs. Lean uses Mathlib's `CliqueFree 4`, `Connected`, vertex degrees, and line graph. [Slater implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/degree.py#L227-L365) · [Matching implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1454-L1489) · [Class predicates](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py)

At inspection the upstream HEAD was the pin `4d1a8afc` and the exact row was proposed with a null proof. Its ID and statement were absent from the three released refutation files and the verified Lean proofs. The inspected maths index had no row 583 entry. Upstream issue 1 addresses ID `f0a6258d`. The 312 distinct released refutation encodings and 4,700 backup graph6 encodings have 4,776 distinct codes in their union. Exactly 586 satisfy the class predicates, including 84 from the refutation files. For every eligible graph the audit script checks the actual Slater prefix and verifies that even the 2(sl−1) largest capacities sum to less than twice the order. This certifies that sl−1 edges cannot suffice by the double-cover lemma. As separate numerical checks, the unmodified GraphCalc optimizers returned Slater, matching and domination values (2,2,3), (2,2,3) and (3,3,5) on examples of orders 10, 38 and 153, respectively. [Release results](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results) · [Inspected maths index](https://github.com/vjdad4m/maths/blob/3de3c30f8a67e30f140febdcaf121fce266e6e14/README.md) · [Issue 1](https://github.com/JanPastorek/AutoGraphForge/issues/1)

Slater's degree-sequence lower bound for vertex domination and the sub-k-domination generalization are established results. The estimate sl(G) ≥ ⌈|V(G)|/(Δ+1)⌉ used for equality is also established. Edge domination and minimum maximal matching have a classical equivalence. A targeted search did not locate the precise minimum-degree-two Slater versus edge-domination inequality with the sharp Eulerian family. This is a source-status check and makes no historical priority claim. [Gentner and Rautenbach on the Slater number](https://www.sciencedirect.com/science/article/pii/S0012365X17300468) · [Amos, Asplund, Brimkov and Davila](https://arxiv.org/abs/1611.02379) · [Desormeaux, Haynes and Henning](https://doi.org/10.1016/j.dam.2014.05.037) · [Yannakakis and Gavril on edge domination](https://doi.org/10.1137/0138030)

## Formal reuse and replay

The five bundled modules `MatchingBasis`, `Row1078`, `Bound`, `FamilyGraph` and `Row574` are unchanged from the row 574 source closure. They supply matching support and maximality from rows 371 and 1883, the actual line-graph domination model and shared-endpoint characterization from row 1078, and the family with both optima from row 574. The endpoint-cover argument in `Row583` adapts row 574. The Slater definition follows rows 33 and 821, and `slater_mass` adapts row 1915's maximum-degree proof. [Row 1078](https://github.com/vjdad4m/maths/tree/3de3c30f8a67e30f140febdcaf121fce266e6e14/autographforge-1078) · [Row 33](https://github.com/vjdad4m/maths/tree/3de3c30f8a67e30f140febdcaf121fce266e6e14/autographforge-33) · [Row 1915](https://github.com/vjdad4m/maths/tree/3de3c30f8a67e30f140febdcaf121fce266e6e14/autographforge-1915)

With Lean 4.19.0 on PATH and a prepared Mathlib v4.19.0 checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, run from the extracted archive

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The script builds all eight modules from source in a fresh directory with warnings as errors and verifies the printed axiom lists for all eight named results. They use only `propext`, `Classical.choice` and `Quot.sound`. The independent data audit uses GraphCalc 2.0.0, NetworkX 3.5 and CBC or another supported MILP solver. The pinned upstream checkout must include the archived Git blobs.

```bash
python check_source.py /absolute/path/to/pinned/AutoGraphForge
```

Expected outputs appear in `Replay.log` and `SourceAudit.log`.
