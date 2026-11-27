# AutoGraphForge row 1160

**Disproved.** A connected triangle-free cubic graph on 22 vertices has vertex clique-cover number 12 and annihilation number 11. Ján Pastorek's normalized physical row 1160 asserts the reverse weak inequality for every finite simple triangle-free cubic graph of order at least two. Its record has ID `4e044e85`, 52 touches and label `promising:class`. [Pinned row](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1160)

## Exactly when the inequality holds

For **every finite triangle-free regular graph of positive degree**, its vertex clique-cover number is at most its annihilation number if and only if it has a perfect matching. The Lean theorem `regular_triangleFree_criterion` uses Mathlib's `Subgraph.IsPerfectMatching` and permits disconnected graphs.

Write n for the order and d for the common degree. Every length-t prefix of the sorted degree sequence sums to td. By the handshaking lemma the edge count is nd/2, so the longest affordable prefix has length ⌊n/2⌋. In a triangle-free graph each clique has at most two vertices. A partition into at most ⌊n/2⌋ cliques must pair every vertex with a distinct neighbor. Conversely, the edges of a perfect matching are such a partition. This also explains why the adjacent physical rows 1161 and 1162, which compare 2θ to the order and 3θ to the size, express the same bound on cubic graphs. The package records a single catalogue result. [Adjacent source rows](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1160-L1162)

## The counterexample

Subdivide one edge in each of three disjoint copies of K₃,₃. Join one new vertex to all three subdivision vertices. Every vertex has degree three. Removing the new vertex leaves three connected components of seven vertices each. A perfect matching would have to use the bridge into every odd component, but all three bridges meet at the new vertex.

Each seven-vertex component requires four cliques, and no clique can meet two different components. Twelve cliques suffice. In each copy of K₃,₃, use a perfect matching avoiding its subdivided edge and put the subdivision vertex in its own class. Add the central vertex to one subdivision-vertex class. Lean verifies this partition, the lower bound, connectivity, the graph class, the sorted-degree computation and the failure of the proposed inequality.

## Implementation, reuse and prior work

GraphCalc 2.0.0 tests nontriviality by order at least two, cubicity by degree three at every vertex, and triangle-freeness by absence of triangles. Its vertex clique-cover routine minimizes the number of colors in the complement. Its annihilation routine sorts degrees in ascending order and finds the longest prefix whose sum is at most the number of edges. The Lean definitions implement these two optimizations. [Class predicates](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py) · [Clique-cover implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/classics.py#L427-L504) · [Annihilation implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/degree.py#L447-L504)

The definition of clique cover is the same complement-coloring infimum used in the published row 1121 and row 464 proofs. The Hall lemma there matches vertices outside a specified dominating set into it. Here the forward implication instead extracts a perfect matching from the two-element fibers of any coloring at the half-order bound. The reverse implication colors vertices by their incident matching edges. [Published row 1121](https://github.com/vjdad4m/maths/tree/385c2df05c643414a0d4855c8a1550c5a6b293ee/autographforge-1121) · [Published row 464](https://github.com/vjdad4m/maths/tree/385c2df05c643414a0d4855c8a1550c5a6b293ee/autographforge-464)

The three odd components are a classical Tutte obstruction. Chartrand, Goldsmith and Schuster give the older 16-vertex cubic example with triangles. Related work by Henning, Löwenstein and Rautenbach proves sharp matching bounds for connected cubic graphs in terms of order and odd girth. This package certifies the catalogue inequality and its matching criterion. Priority for the graph and the matching argument is unclaimed. [Tutte (1947)](https://doi.org/10.1112/jlms/s1-22.2.107) · [Chartrand, Goldsmith and Schuster (1979), p. 341](https://doi.org/10.4064/cm-41-2-339-344) · [Henning, Löwenstein and Rautenbach (2012)](https://doi.org/10.1016/j.disc.2012.03.002)

The pinned release labels this ID proposed with a null Lean proof. The exact statement and ID are absent from all three refutation files and the released verified proofs. Of 312 distinct released graph6 encodings, 31 are nontrivial and cubic and 16 are also triangle-free. For each eligible graph the audit constructs a perfect matching, checks every edge and verifies that its size equals GraphCalc's annihilation number. The four tracked graph6 backup files have identical contents, with 4,700 more encodings before deduplication. Across the union there are 4,776 encodings, 118 nontrivial cubic graphs and 56 eligible graphs. All 56 have checked perfect matchings. Thus none of these published graphs refutes row 1160. The inspected public maths index contained no 1160 entry and the single inspected upstream issue concerned a different ID. [Release](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results) · [Shared index](https://github.com/vjdad4m/maths/blob/385c2df05c643414a0d4855c8a1550c5a6b293ee/README.md) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1)

## Replay

Use Lean 4.19.0 on PATH and a prepared Mathlib v4.19.0 checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. If the matching module is missing from a partial cache, run `lake build Mathlib.Combinatorics.SimpleGraph.Matching` in the Mathlib checkout. From the extracted source directory run

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The script compiles both modules from source into a fresh directory with warnings as errors and verifies seven printed axiom lists. All seven contain exactly `propext`, `Classical.choice` and `Quot.sound`.

The independent source audit uses GraphCalc 2.0.0 and NetworkX 3.5. The default check obtains the lower bound from the original clique-cover optimizer on each lobe, verifies the 12-class partition on the full graph and calls the original annihilation routine on the full graph. The optional `--full-milp` also invokes the original unrestricted clique-cover optimizer on all 22 vertices. Run

```bash
python check_source.py /absolute/path/to/pinned/AutoGraphForge
```
