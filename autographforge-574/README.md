# AutoGraphForge row 574

**Disproved.** Ján Pastorek's normalized physical row 574 proposes that every nontrivial Eulerian triangle-free graph has domination number at most its minimum maximal matching number. A 10-vertex graph has respective values 3 and 2. More generally, for every integer k ≥ 2 a connected Eulerian triangle-free graph attains γ(G) = 2k−1 and γ(L(G)) = k. This is the largest possible domination number for that value of k. [Pinned row 574, ID 07b76d4b](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L574)

## The ten-vertex witness

Start with two disjoint edges ab and cd. For each of ac, ad, bc and bd insert a fresh vertex adjacent to its two indicated endpoints. For ad and bc add a second such vertex. The four original vertices have degree four and the six new ones have degree two. The graph is connected. A triangle would require a common neighbor of the two ends of one original edge, and there is none.

The edges ab and cd form a maximal matching and dominate the line graph. Row 1078's triangle-free minimum-degree lower bound gives γ(L(G)) ≥ 2. Any three of the four original vertices dominate. No two vertices dominate: two originals from one pair miss the other pair, and two from different pairs miss a connector joining the omitted originals. One original vertex has a closed neighborhood of size five and a connector has a closed neighborhood of size three, so a pair containing a connector covers at most eight vertices. The Lean theorem `EulerDom574.Compact.witness` checks the class and all three optima, including the independently defined minimum size of a maximal matching.

## The sharp bound and its family

Let G be any nonempty finite simple graph with minimum degree at least two, and let D be a minimum edge-dominating set. Its endpoint set T meets every edge and has size at most 2|D|. Delete one vertex x from T. The vertex x still sees its partner on a selected edge. Every vertex outside T has at least two distinct neighbors in T, so at least one remains. Consequently γ(G) + 1 ≤ 2γ(L(G)). Every connected even-degree graph of order at least two has minimum degree at least two. Lean proves both versions in `upper` and `eulerian_upper`.

For each k ≥ 2, start with k disjoint core edges, labeling their 2k endpoints by a pair index and a bit. For every ordered pair of cores from distinct core edges, add 2k new vertices adjacent precisely to those two cores. For each index i, add one further vertex joining the false endpoint of pair i to the true endpoint of pair i+1 modulo k. This gives each core even degree. New vertices have degree two, the graph is connected, and no new vertex sees both ends of one core edge. The original k edges are a maximal matching. Each graph edge can dominate at most one original edge, so both edge optima equal k.

A dominating set with fewer than 2k−1 vertices cannot omit cores from two different pairs. It would have to contain every one of their 2k common connectors. If all omitted cores lie in one pair, the cardinality budget forces the selected vertices to be precisely the other 2k−2 cores. These fail to dominate the omitted pair. The lower bound 2k−1 and the universal upper bound coincide. See `EulerDom574.family` for the full statement quantified over k = n+2 and `EulerDom574.row574_false` for the negation of the catalogue statement.

## Source conventions and reuse

GraphCalc 2.0.0 computes vertex domination by minimizing over sets meeting every closed neighborhood. It implements `min_maximal_matching_number(G)` by calling `domination_number(nx.line_graph(G))`. Nontrivial means at least two vertices. On undirected graphs the Eulerian predicate requires connectivity and even degrees. Triangle-freeness excludes three pairwise adjacent vertices. Lean uses Mathlib's actual line graph and proves both matching parameter values for the constructed graphs. [Domination implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L84-L185) · [Matching implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1454-L1489) · [Class predicates](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py) · [NetworkX Eulerian predicate](https://networkx.org/documentation/networkx-3.5/reference/algorithms/generated/networkx.algorithms.euler.is_eulerian.html)

The bundled `Row1078.lean` supplies the edge-domination definition, the shared-endpoint characterization and the triangle-free minimum-degree lower bound. Its `MatchingBasis.lean` reuses the published row 371 endpoint-support and matching extension lemmas and the row 1883 maximal-matching definition. Both imported modules are unchanged. The general family uses the k distinguished edges directly for its sharp lower bound. [Published row 371](https://github.com/vjdad4m/maths/blob/0965fd58d3027e10c30295a29229aad7d9cb1779/autographforge-371/AutoGraphForge371.lean) · [Published row 1883](https://github.com/vjdad4m/maths/blob/0965fd58d3027e10c30295a29229aad7d9cb1779/autographforge-1883/AutoGraphForge1883.lean)

## Prior work and released witnesses

The pinned record has 163 touches, classification `promising:class`, status `proposed` and a null Lean proof. The inspected maths index, the released verified proofs and the three refutation files had no result for this row. Upstream issue 1 addresses a different ID. The three refutation files give 312 distinct graph6 codes. Four identical backups contribute 4,700 codes, with 4,776 distinct codes in their union. Of these, 327 satisfy the row hypotheses, including 69 from the refutation files. All 327 satisfy the inequality. [Pinned release](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results) · [Inspected maths index](https://github.com/vjdad4m/maths/blob/2a579a058f2b1496ac9cd0a99310e947eda00dc5/README.md) · [Upstream issue 1](https://github.com/JanPastorek/AutoGraphForge/issues/1)

For each eligible encoding, `check_source.py` verifies a vertex-dominating set S. In 303 cases its size is at most either the row 1078 minimum-degree lower bound or the number of edges divided by the largest closed edge-neighborhood size, rounded up. In the remaining 24 it branches over the possible dominators of an uncovered edge to rule out covering the line graph with |S|−1 edges. It also calls the upstream implementations on the 10-vertex witness and the k = 2, 3 family members. The general result is kernel-checked independently of this numerical audit.

The equality of minimum maximal matching size and edge domination number is classical. Baste, Fürst, Henning, Mohr and Rautenbach studied the inequality on regular graphs. Their Figure 1 already shows failure for an irregular graph with edge domination number one, outside the present domain by the bound above. Their Figure 2 uses cross-neighbors of two matched edges, related to the ten-vertex construction. Afrasyab subsequently exhibited a cubic counterexample to the regular conjecture, whose odd degrees exclude it here. The known positive theorem for claw-free graphs of minimum degree two also has different hypotheses. These sources establish relevant prior results. Historical priority for the Eulerian triangle-free family or the sharp replacement bound remains unverified. [Yannakakis and Gavril](https://doi.org/10.1137/0138030) · [Baste et al.](https://arxiv.org/pdf/1906.10420) · [Afrasyab](https://arxiv.org/abs/2609.10783) · [Claw-free theorem](https://doi.org/10.1016/j.dam.2023.05.002)

## Replay

With Lean 4.19.0 on PATH and a prepared Mathlib v4.19.0 checkout at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, run from the extracted archive

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The replay builds all six modules from source into a fresh temporary directory, treats warnings as errors and checks the printed axiom lists. The only axioms reported for the results are `propext`, `Classical.choice` and `Quot.sound`. If using a partial Mathlib cache, ensure `Mathlib.Combinatorics.SimpleGraph.LineGraph` and its imports are built. To reproduce the independent source and data audit, use GraphCalc 2.0.0, NetworkX 3.5 and a supported MILP solver such as CBC, then run

```bash
python check_source.py /absolute/path/to/pinned/AutoGraphForge
```

The checkout must contain the pinned Git objects, including the graph6 backups. The expected outputs are in `Replay.log` and `SourceAudit.log`.
