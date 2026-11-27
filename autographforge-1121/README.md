# AutoGraphForge row 1121

**Proved.** Every finite simple graph of order at least two and maximum degree at most three has vertex clique-cover number at most its singleton three-rainbow domination number. Disconnected graphs and isolates are included. This is normalized physical row 1121, generated ID `6deb0d7d`, in Ján Pastorek's AutoGraphForge catalogue. [Pinned row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1121)

## Proof and sharpness

Let S be the colored vertices in a feasible singleton k-rainbow labeling, where k is positive. Any uncolored vertex sees k distinct vertices of S, one of each color. If all degrees are at most k, every vertex in S has at most k uncolored neighbors. For any set X of uncolored vertices, let N be its neighbors in S. Counting the edges between X and N gives k|X| ≤ k|N|. Hall's theorem supplies a matching of all the uncolored vertices into S. Each matched edge is a two-vertex clique, and the remaining vertices of S give singleton cliques. This partitions the whole graph into exactly |S| cliques. Minimizing over the labelings proves the result. The argument also applies to the empty graph and to a single vertex. [P. Hall, *On Representatives of Subsets* (1935)](https://doi.org/10.1112/jlms/s1-10.37.26)

The reusable lemma `match_outside` only requires that each vertex outside S has at least k neighbors in S and each vertex in S has at most k neighbors outside. The theorem `rainbow_bound` specializes it to every finite simple graph of maximum degree at most k. The catalogue statement is `row1121`.

For positive k and m ≥ k, the complete bipartite graph K(k,m) has clique-cover number m and singleton k-rainbow domination number k. Give the vertices in the k-part distinct colors. Conversely, either the entire k-part is colored, or a zero in it sees k distinct colored vertices. The larger part is independent, so every clique partition needs m slots. Pairing the smaller part with distinct vertices in the larger part attains this bound. Lean verifies both values and the degree of every vertex. Thus K(3,3) attains equality, K(3,4) fails the inequality at maximum degree four, and the gap on K(3,m) is m−3.

## Catalogue, implementation and prior work

The pinned entry has 62 touches, label `promising:class`, status `proposed`, and a null Lean proof. Its ID and exact statement are absent from the three released refutation files and released verified Lean proofs. At the inspected public maths commit, the README and recursive file tree contained no row 1121 entry. The upstream issue concerned a different ID. The audit below verifies the physical line, generated record and release files. [Generated records](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_results.json) · [Release](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results) · [Public maths index](https://github.com/vjdad4m/maths/blob/e5b94f84920cf9c321577269e505cb5c8acd14cd/README.md) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1)

GraphCalc minimizes the number of colored vertices, assigns each vertex at most one color, and requires every uncolored vertex to see all three colors among its neighbors. It computes the vertex clique-cover number by optimally coloring the complement. Subcubic means maximum degree at most three. The proof generalizes the singleton-label definitions used for rows 720 and 1707 and uses the complement-coloring definition and color-class construction used for row 621. The incidence counting previously used on cycles only controlled the total number of colored vertices. Applying it on each subset and invoking Mathlib's finite Hall theorem gives the clique partition. [GraphCalc rainbow optimizer](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1159-L1201) · [Three-rainbow wrapper](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1306-L1337) · [Clique-cover optimizer](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/classics.py#L427-L504) · [Subcubic predicate](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py#L766-L791) · [Row 621](https://github.com/vjdad4m/maths/tree/e5b94f84920cf9c321577269e505cb5c8acd14cd/autographforge-621)

Targeted searches for singleton rainbow domination, clique partitions, edge covers and matching bounds located degree-and-order lower bounds for regular graphs and singleton bounds for cylindrical graphs. Those results give numerical bounds for different classes or parameters. I found no prior statement of the exact clique-cover inequality in the sources checked. The matching argument is a consequence of classical Hall theory, and the status audit establishes no historical priority. [*On k-rainbow domination in regular graphs* (2020)](https://doi.org/10.1016/j.dam.2020.04.003) · [J. Žerovnik, *On Singleton 3-Rainbow Domination of Cylindrical Graphs* (2026)](https://doi.org/10.3390/math14162917)

## Independent release-witness check

Of the 312 distinct released graph6 witnesses, 125 are nontrivial and subcubic. All 125 satisfy the conjecture by explicit finite bounds. A matching in the whole graph gives a clique partition into its edges and unmatched singletons. Every uncolored vertex has degree three and three colored neighbors. Thus the uncolored vertices are independent in the degree-three subgraph. A second edge-and-singleton partition of that subgraph gives an upper bound on the number of uncolored vertices. The script checks both matchings and confirms that the resulting clique upper bound never exceeds the rainbow lower bound. Validity of the certificates only uses the matching property.

The same script runs the pinned GraphCalc optimizers directly on K(3,3), K(3,4), K(3,7), and K(3,3) with an isolate.

## Replay

Use Lean 4.19.0 on PATH and Mathlib v4.19.0 at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, with the imported Mathlib modules built. From the extracted archive run

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The script builds both modules in a fresh temporary directory with warnings as errors and checks the printed axiom lists for seven results. Each uses only `propext`, `Classical.choice` and `Quot.sound`.

The separate audit requires GraphCalc 2.0.0, NetworkX 3.5, a supported optimization solver and the pinned upstream checkout.

```bash
python check_source.py /absolute/path/to/pinned/AutoGraphForge
```
