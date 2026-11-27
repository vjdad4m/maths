# AutoGraphForge row 464

**Disproved.** A connected bipartite planar graph on 11 vertices has vertex clique-cover number 6 and singleton three-rainbow domination number 5. More generally, for every integer m ≥ 2 the family below has order 3m+2 and these invariants are respectively 2m and m+2. Every nonnegative additive gap occurs. Ján Pastorek's normalized physical row 464 requires only order at least two, K₄-freeness and planarity. [Pinned row 464](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L464)

## Family and proof

Start with two hubs. For each of m groups, add two outer vertices and a center. Each outer vertex is adjacent to both hubs and to its own center. These are all the edges. The hubs and centers lie on one side of a bipartition and the 2m outer vertices lie on the other. The graph is connected and K₄-free.

* **Clique cover.** The independent set of 2m outer vertices requires at least 2m cliques. Pair each center with the first outer vertex in its group, then pair the two hubs with the second outer vertices from two distinct groups. The unmatched vertices form singleton cliques. This gives exactly 2m.
* **Singleton three-rainbow domination.** Give the hubs colors 1 and 2 and every center color 3. Every outer vertex sees all three colors. Conversely, every center has degree two and must be colored. If both hubs are colored, that already costs m+2. If either hub is uncolored, every outer vertex must be colored because it has only two other neighbors. Since 2m ≥ m+2, the optimum is m+2.
* **Planarity.** Place the hubs at (−1,0) and (1,0). For group i, place the first outer vertex, center and second outer vertex at (0,3i), (0,3i+1) and (0,3i+2). Draw straight segments. Left and right spokes have interiors in disjoint open half-planes. On either side the horizontal coordinate determines the segment parameter, and then its height determines the endpoint. The open vertical segments occupy distinct intervals between consecutive integer heights. The Lean drawing checks embedded arcs, orientation reversal, vertex avoidance and every interior intersection for arbitrary m.

`Row464.lean` proves the negation of the complete catalogue statement. `family` records both invariant values and every class hypothesis. `unbounded` proves that the gap can equal any prescribed natural number. All three are unconditional.

## Sharp bound and its formal scope

Write θ for the clique-cover number and r for the singleton three-rainbow number. The same family attains **θ = r + max(0,r−4)** for every r ≥ 4. A matching argument gives the corresponding upper bound for all planar graphs.

For a feasible labeling, let S be its colored set of size b. For a nonempty subset X of its uncolored vertices, let N be its neighbors in S. Each vertex in X sees three distinct colors, so the bipartite graph of incidences between X and N has at least 3|X| edges. This finite simple planar graph has at least four vertices. The usual bipartite planar edge bound gives at most 2(|X|+|N|)−4 edges. Consequently |X|−|N| ≤ |N|−4 ≤ b−4. Add max(0,b−4) dummy neighbors shared by all uncolored vertices. Hall's theorem matches every uncolored vertex either to a colored neighbor or to a dummy. Matched real pairs form cliques, dummy matches give singletons, and unused real vertices give singletons. Minimize b to obtain the bound. [P. Hall, *On Representatives of Subsets*](https://doi.org/10.1112/jlms/s1-10.37.26) · [Bipartite planar edge bound](https://drdebmath.github.io/IITIJan2026CS637/lecture23.html)

`SharpBound.lean` proves the Hall argument under the explicit cross-edge inequality `CrossEuler`. The step from a general topological drawing to that Euler inequality uses the classical planar edge theorem in the written proof. This step has no Lean formalization in this package. `Row464.lean` proves the counterexample, unbounded gap and attainment directly and does not import `SharpBound.lean`.

## Source, related work and independent checks

The pinned normalized record has ID `f488855f`, 220 touches, label `promising:class`, status `proposed` and no Lean proof field value. Its exact statement and ID are absent from the three refutation files and released verified proofs. The public maths README and recursive file tree at the inspected revision contained no physical row 464 entry. The only upstream issue concerned a different ID. Searches for the exact invariant pair and for singleton three-rainbow domination, clique partitions and planar bipartite graphs found results on cylindrical graphs but no earlier resolution of this precise row. This is a release and literature check with no priority claim. [AutoGraphForge records](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results) · [Inspected public index](https://github.com/vjdad4m/maths/blob/596c9d1d0bfa977a8728397c8cf5339ea80755a6/README.md) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1) · [Žerovnik, *On Singleton 3-Rainbow Domination of Cylindrical Graphs*](https://doi.org/10.3390/math14162917)

The source closure includes the row 1121 `../autographforge-1121/HallRainbow.lean` definitions without changes. That theorem assumes maximum degree at most three. Here the hubs have degree 2m. Row 1707 concerned claw-free graphs. Here either hub sees an independent set of 2m neighbors. The real-plane drawing structure and straight-segment embedding lemmas follow rows 357 and the cycle batch, with new separation arguments for this family. [Published drawing template](https://github.com/vjdad4m/maths/blob/596c9d1d0bfa977a8728397c8cf5339ea80755a6/autographforge-357/AutoGraphForge357.lean)

GraphCalc 2.0.0 uses optimal coloring of the complement for vertex clique cover. The rainbow model assigns at most one color to each vertex, requires each uncolored vertex to see all three colors and counts colored vertices. Its planar predicate calls NetworkX planarity testing. Its K₄-free predicate checks neighborhoods for triangles. [Clique-cover implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/classics.py#L427-L504) · [Singleton rainbow optimizer](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1159-L1201) · [Three-color wrapper](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1306-L1337) · [Graph classes](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py)

All 148 eligible graphs among the 312 released graph6 witnesses satisfy row 464. Each has an explicit checked coloring of the complement. For 137 graphs a lower bound on the rainbow number reaches the size of that coloring. Vertices of degree less than three must be colored. For b colored vertices the total degree of the selected vertices must cover at least 3(n−b) incidences. For the remaining 11 graphs, the script generates a singleton-rainbow CNF with a prefix cardinality bound, and checks every unit-propagation hint of CaDiCaL's LRAT refutation in Python. The same entry point runs the original GraphCalc class tests and both optimizers at m=2,3,4.

## Replay

From the extracted archive use Lean 4.19.0 and a prepared Mathlib v4.19.0 checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Run

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The script builds all five modules in a fresh temporary directory with warnings as errors and checks the printed axiom lists of ten results, including the exact disproof. Each uses only `propext`, `Classical.choice` and `Quot.sound`.

The independent audit uses GraphCalc 2.0.0, NetworkX 3.5, a supported optimization solver and the CaDiCaL binary provided with Lean 4.19.0. Set CADICAL to its absolute path if necessary.

```bash
python check_source.py /absolute/path/to/pinned/AutoGraphForge
```
