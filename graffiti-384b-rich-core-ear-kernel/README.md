# Graffiti.pc #384b on the score-one ear core

Let J consist of the triangle edges of a finite simple graph G, with the same vertex set. A vertex is rich if it lies in at least two triangles. A score-one vertex has exactly two neighbors in J. Write t for the number of distinct triangle counts in G, including zero when it occurs. The catalogue asks whether γ₂(G) ≤ |V(G)| − ⌈t/2⌉ for every connected G on more than two vertices. A 2-dominating set provides at least two neighbors for each vertex outside it.

**If the triangles of the subgraph induced by the rich vertices are vertex-disjoint, every connected G of order greater than two satisfies the catalogue bound.** More generally, in any hypothetical failure, deleting all score-one vertices loses at most two incident triangles at each retained vertex. For a connected graph of order greater than two that fails the bound, some rich vertex lies in at least t−3 triangles consisting entirely of rich vertices. These statements use no order or diversity cutoff. [EarTriangleLoss.lean](EarTriangleLoss.lean)

Every internal triangle count is shared by at most three rich vertices in a failure, since their distinct original scores can increase from this internal value by at most two. With score one present, the rich-induced subgraph therefore realizes at least ⌈(t−2)/3⌉ different internal counts. Four rich vertices with a common internal triangle count already guarantee the catalogue inequality. For connected graphs of order greater than two, the inequality also holds whenever that internal triangle count is constant on each connected component of the subgraph induced by rich vertices. This includes components that are cliques of arbitrary size. [RichCore.lean](RichCore.lean)

## Independent ears and matchings

Choose any family F of score-one vertices independent in J. Let A be the set of their distinct rich neighbors, W the rich vertices outside A, and K the complement of F∪W. In a failure with score one, put d=2|F|−|A|. The following necessary conditions apply simultaneously to every such choice.

* d is zero or one. There is a matching of actual triangle edges in J[W] missing exactly 1−d vertices. A repeated anchor, or an incidence with a nonrich neighbor, uses the entire allowance.
* For each single ear e there is a perfect matching of the induced triangle graph on the rich vertices together with e. More precisely, every certified split of this set admits a perfect matching using the specified two-neighbor certificates in either direction. This concerns the cut on the rich vertices and e. The preceding matching on W uses a different vertex set.
* At most 14 vertices in W have two or more original neighbors in K. If d=1 there are at most six, each adjacent by a triangle edge to a rich cubic with no original neighbor in K. The at most two such cubics have distinct scores in {2,3}. The retained set K includes the leaf in a rooted single-leaf instance whenever F and W consist of positive-score vertices.

The proof fixes all ears in F as omissions and keeps the anchors. Both shores of a suitable cut of W supply valid omission sets together with F. A subset of one shore may replace every opposite neighbor used by its chosen certificates, including contacts with certificates chosen in the other direction. A strict Hall deficiency would increase the omission count. The finite Hall theorem therefore yields the stated matching. If three incident triangles at the same center each used a score-one endpoint, those three endpoints would be independent ears sharing one anchor, contradicting d≤1. This proves the triangle-loss bound. [SupportHall.lean](SupportHall.lean) · [EarFootprint.lean](EarFootprint.lean) · [EarPairing.lean](EarPairing.lean) · [EarTriangleLoss.lean](EarTriangleLoss.lean)

For the numerical donor bounds, fix additional omissions X among vertices of W with two original neighbors in K. Once |A|+2≤2|F|+|X|, failure requires a remaining vertex v with degree in J plus its original neighbors in K strictly less than three plus its neighbors in X in J. With d=1 a single omission forces a cubic obstruction. For every pair outside all such cubic neighborhoods, both vertices must be neighbors of a rich vertex of degree at most four in J. At most five such vertices have distinct scores, all in {2,…,6}. They can cover at most 30 pairs, allowing at most eight additional vertices besides the six cubic neighbors. [EarDonors.lean](EarDonors.lean) · [EarDonorPairs.lean](EarDonorPairs.lean)

For any family of pairwise disjoint sets with no triangle edge between different sets, the guaranteed omission counts on the sets add. On each set count its rich vertices, add one if a score-one vertex occurs, and round half of the resulting sum upwards locally. A failure imposes the corresponding separator parity restriction. [EarPacking.lean](EarPacking.lean) · [SeparatorParity.lean](SeparatorParity.lean)

The checked theorem `catalogue_iff_remaining` restricts the earlier single-leaf reduction at every order cutoff to rooted cores passing the matching, donor, and per-vertex triangle-loss tests. The root can be any core vertex. The connected single-leaf cases passing all the tests remain open here. [EarKernel.lean](EarKernel.lean)

## Exact nine-vertex example

Start with the six-vertex graph6 graph `EQzw`. Attach one triangular ear on each of the edges 0–5 and 4–5, then add a leaf at 0. The vertex scores in label order are 4,2,3,1,5,7,1,1,0. For F={6,7} the three rich anchors are {0,4,5}. The two residual vertices 1 and 2 are nonadjacent, so the perfect residual matching required in a failure does not exist. A 2-dominating set is {0,1,4,5,8}. Lean checks that none has fewer than five vertices. The example attains the catalogue bound. A targeted external search suggested its adjacency list. Lean checks that list, connectedness, the anchor and residual sets, all scores and the optimum directly. The search supplies no coverage theorem. [EarExampleNine.lean](EarExampleNine.lean)

A separate Python check on three fixed graphs illustrates the scope of the uncolored matching test. On an eleven-vertex graph with nine distinct scores, every independent ear family passes the incidence count while the family of all three ears fails the residual matching condition. On an eight-vertex graph with seven distinct scores, every family passes both uncolored matching tests, and the optimum still attains the bound. These two additional calculations are external diagnostics. The script exhausts the dominating sets and matchings only on its three explicit inputs. [Diagnostic checker](check_fixtures.py)

## Replay and reuse

The embedded 88-module predecessor is the exact source archive inside the published missing-one release. The GitHub release blob and the local release blob both have OID `20ab605e34bf15d0ff0375b352d0495aab1a2098`. This stage reuses its triangle pruning, rich-score injectivity, local omission capacities, `Repair.seeded_cut`, and the finite Hall theorem in `HallFiniteBase`. That Hall module was previously checked with the #189 linkage transfer. The matching proof here uses its finite transversal theorem directly. No disjoint-path extraction is required. [Published predecessor](https://github.com/vjdad4m/maths/tree/main/graffiti-384b-missing-one)

Set `CROSSFOUR_LEAN_BIN` to the Lean 4.19.0 binary directory and `CROSSFOUR_MATHLIB` to built Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. In the extracted source archive run

~~~sh
python3 -B replay_ears.py
~~~

A segmented run may use `--predecessor-log /absolute/path/to/CompleteCold.log`. It verifies all 88 predecessor object hashes before rebuilding the eleven new modules. Warnings are errors, and the axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`. The source manifest lists every one of the 99 project modules and its exact hash. [All project sources](ALL-SOURCES.tsv) · [Replay entry point](replay_ears.py) · [New object hashes](OBJECTS.sha256)

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
