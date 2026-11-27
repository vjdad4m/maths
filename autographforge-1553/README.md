# AutoGraphForge row 1553 and a sharp bound beyond subcubic graphs

**Row 1553 holds.** Every finite simple subcubic graph of order at least two with a numerical edge cover value satisfies ρ ≤ r₃, where ρ is the minimum edge cover size and r₃ is the singleton three-rainbow domination number. The connected graph K₃,₃ attains equality with both values equal to three. An isolate prevents an edge cover and yields a missing catalogue cell. The inequality includes disconnected graphs on its numerical domain. [Ján Pastorek’s normalized physical row 1553, ID 8a00807b](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1553)

For every positive k and every finite isolate-free simple graph, let rₖ be its minimum number of colored vertices under singleton k-rainbow domination. Write (t)₊ = max(0,t). The stronger theorem is

$$\rho(G) \le r_k(G) + \left\lfloor \frac{1}{k}\sum_{v\in V(G)} (\deg v-k)_+ \right\rfloor.$$

In particular, total excess less than k still gives ρ ≤ rₖ. For example, the three-color inequality remains valid if two vertices have degree four and every other vertex has degree at most three. For 1 ≤ k ≤ m, the complete bipartite graph Kₖ,ₘ has ρ = m, rₖ = k, and total excess k(m − k). These graphs attain every nonnegative integral gap, including equality at the degree threshold. K₃,₄ already fails the uncorrected inequality at maximum degree four.

## Proof

Let S be any k-dominating set, meaning that each vertex outside S has at least k neighbors in S. For u ∈ S write dₒ(u) for its number of neighbors outside S. The proof gives the more local bound

$$\rho(G) \le |S| + \left\lfloor \frac{1}{k}\sum_{u\in S}(d_o(u)-k)_+ \right\rfloor.$$

Take a subset X of the outside vertices and let N be its neighbors in S. At least k|X| edges join X to N. Counting at the other end gives at most k|N| plus the sum of positive excess loads over S. Thus |X| − |N| is at most the integer correction d in the local bound.

Add d auxiliary representatives available to every outside vertex. Hall’s theorem now assigns distinct representatives to all outside vertices. A vertex assigned a real neighbor is covered together with it by their joining edge. For each unused real representative choose any incident edge. For each outside vertex assigned an auxiliary representative choose any incident edge. Since every vertex has an incident edge, these choices form an edge cover using at most |S| + d edges. This is the classical deficiency form of the representatives argument. [P. Hall, *On Representatives of Subsets*](https://doi.org/10.1112/jlms/s1-10.37.26)

For a singleton k-rainbow labeling, its colored vertices form a k-dominating set. Distinct colors require distinct neighbors. Bounding each outside load by the full degree and minimizing over labelings gives the stated inequality. Subcubic graphs have zero degree excess at k = 3.

For sharpness on Kₖ,ₘ, the m vertices of the larger part are independent, so each covering edge meets only one of them. Coloring the k vertices of the smaller part in distinct colors gives a rainbow labeling of weight k. Conversely, a labeling either colors the whole smaller part or has an uncolored vertex there that needs k colored neighbors. The Lean proof reuses the checked biclique rainbow and clique-cover formulas and proves that a minimum edge cover gives a clique partition with at most as many classes. The upper bound supplies the matching value ρ = m.

## Catalogue and prior work

The pinned default branch was at `4d1a8afc99447cacd2328cca20e47b6493e8dbc5`. The exact CEGIS record was marked `proposed` with a null Lean proof. The normalized row had 37 touches and the annotation `promising:class`. The ID and statement were absent from the three released refutation files and the verified Lean files. The inspected public maths README at `cd183c14fcfd0c44c26ef2101473ff405652581b` contained neither the row number nor its ID. The only upstream issue concerned a different ID. [Release records](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results) · [Inspected shared index](https://github.com/vjdad4m/maths/blob/cd183c14fcfd0c44c26ef2101473ff405652581b/README.md) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1)

Row 1121 proved the analogous clique-cover inequality by matching every uncolored vertex to a distinct colored neighbor under a degree bound. Its matching argument also gives the zero-excess case for edge covers once unused colored vertices receive incident edges. A clique cover alone can be smaller than an edge cover. The triangle has clique-cover number one and edge cover number two. The general result here bounds the unmatched vertices when the degree condition fails. Row 464 previously used auxiliary Hall representatives for a planar incidence budget. Here the budget follows directly from a finite double count on every graph and has no planarity hypothesis. [Row 1121 and biclique formulas](https://github.com/vjdad4m/maths/tree/cd183c14fcfd0c44c26ef2101473ff405652581b/autographforge-1121) · [Row 464 deficient Hall construction](https://github.com/vjdad4m/maths/tree/cd183c14fcfd0c44c26ef2101473ff405652581b/autographforge-464)

Related literature treats k-domination, and Žerovnik studies the same singleton labeling convention on cylindrical graphs. Searches for edge cover, singleton rainbow domination, k-domination and degree-excess matching bounds found no prior statement of the exact excess inequality. This search establishes no historical priority. [k-domination in bipartite graphs](https://doi.org/10.1515/math-2020-0047) · [Žerovnik, *On Singleton 3-Rainbow Domination of Cylindrical Graphs*](https://doi.org/10.3390/math14162917)

## Source and numerical audit

GraphCalc 2.0.0 defines nontriviality by order at least two and subcubicity by maximum degree at most three. Its rainbow optimizer permits each vertex either one color or zero. Each zero must see all k colors in its open neighborhood. The objective counts the colored vertices. Its edge cover routine takes the size of the NetworkX minimum edge cover. NetworkX raises on an isolate, and AutoGraphForge’s battery leaves that entry missing. Lean represents the missing value with `none`. [Subcubic definition](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py#L766-L791) · [Singleton optimizer](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1159-L1201) · [Three-color wrapper](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/domination.py#L1306-L1337) · [Edge cover wrapper](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/classics.py#L628-L655)

The audit tested all 4,776 distinct graph6 encodings in the named refutations and four identical backups. Of 1,174 that met the predicates, 375 contained isolates and 799 had numerical values. All 799 satisfied the inequality. Each uncolored vertex in a subcubic graph has degree three and all of its neighbors are colored. Consequently every vertex of degree below three is colored, and every matched pair in the subgraph of degree-three vertices needs at least one colored endpoint. On each input the computed edge cover was at most the resulting lower bound on rainbow domination. The original public `compute_battery` entry point also confirmed both optimizer values on K₃,₃, K₃,₄, and K₃,₇, and the missing cell on two isolates. [Pinned battery](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/pipeline/invariants_graphcalc.py)

## Lean sources and replay

`Deficiency.lean` proves the local incidence count, the edge cover construction from Hall deficiency, and the k-dominating set bound. `Row1553.lean` gives the label-independent excess bound, exact catalogue row and sharp family. `HallRainbow.lean` and `Boundary.lean` are the published row 1121 modules, and `Cover.lean` supplies the row 1125 edge cover and missing-value definitions. These three files were matched byte-for-byte with the inspected public repository. All imported project sources are included. [Published edge cover definitions](https://github.com/vjdad4m/maths/blob/cd183c14fcfd0c44c26ef2101473ff405652581b/autographforge-1125/Cover.lean)

With Lean 4.19.0 on PATH and a built Mathlib 4.19.0 checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, run in the extracted directory

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The script rebuilds all ten modules with warnings as errors and checks the axiom lists of eight result theorems. Each uses only `propext`, `Classical.choice`, and `Quot.sound`. To repeat the release and numerical audit, use GraphCalc 2.0.0 and NetworkX 3.5 with a supported MILP solver and the pinned checkout containing the backup graph6 blob.

```bash
python audit.py /absolute/path/to/AutoGraphForge
```

The expected outputs are in `Replay.log` and `SourceAudit.log`.
