# Graffiti.pc #384b with odd diversity and a realized zero

For a finite simple graph G on n vertices, let T be the set of distinct numbers of triangles through a vertex. The catalogue asks whether γ₂(G) ≤ n − ⌈|T|/2⌉ for connected G with n > 2. A two-dominating set contains at least two neighbors of every vertex outside it. The results below hold in the original graph at every order, including disconnected graphs.

Call a graph a *failure* if γ₂(G) > n − ⌈|T|/2⌉. The frozen positive-palette bound gives 2γ₂(G) + |T ∖ {0}| ≤ 2n. Hence a failure has odd diversity and realizes zero. This package gives necessary conditions for failure and proves the catalogue inequality for several subcases.

## Necessary conditions in the original graph

* Every vertex with triangle count at least two has a count different from every other vertex. Every zero-count vertex has degree at most two. A count-one vertex of degree at least three must be the only count-one vertex. [OddStarFrontier.lean](OddStarFrontier.lean)
* Suppose some zero-count vertex z has degree two. The count one occurs, and every vertex realizing it is a degree-two triangular ear. Writing H for the set of vertices of degree at least three, H consists exactly of vertices with count at least two and |T| = |H| + 2. All degree-two vertices have both neighbors in H. If there are d degree-two vertices, their 2d incidences have at least 2d−1 distinct endpoints. [ZeroTwoLayout.lean](ZeroTwoLayout.lean)
* Every neighbor of z is connected to every count-one ear by edges lying in triangles. If we restore the two original edges at z, then z stays connected to every such ear after deleting any third vertex. Even in the absence of degree-two zeros, every two distinct vertices of count one stay connected by triangle edges after deleting any third vertex. [ComponentBalance.lean](ComponentBalance.lean) · [TriangleBlocks.lean](TriangleBlocks.lean)
* A degree-two zero and a count-one ear have disjoint neighborhoods in every failure. A common anchor would give a route from z to the ear avoiding the anchor. If the route length is odd, a triangle on its second edge changes its parity without using the anchor. The resulting even cycle simultaneously protects the zero and the ear. [SharedZeroAnchor.lean](SharedZeroAnchor.lean)
* A degree-two zero and a count-one vertex cannot both lie on four-cycles in a failure. Also, two count-one vertices on four-cycles must have intersecting neighborhoods. The squares can overlap. For distinct second centers the proof reverses the relative colors of the square frames. For a common second center it gives both original centers the same color. [CoupledSquares.lean](CoupledSquares.lean) · [SquareObstructions.lean](SquareObstructions.lean)

* In a failure with a degree-two zero, at most two degree-two vertices in the entire graph can lie on four-cycles. For any collection of such vertices the anchor pairs intersect pairwise, so their union has size at most one more than the size of the collection. The low-support estimate rules out a collection of size three or more. [SquareCensus.lean](SquareCensus.lean)
* If two degree-two vertices do lie on four-cycles in that branch, both are count-one ears. Their neighborhoods are {c,a} and {c,b} for three pairwise adjacent vertices a,b,c. Thus if a degree-two zero lies on a four-cycle, every other degree-two vertex lies on no four-cycle. [SquareTriangle.lean](SquareTriangle.lean)

## Cut and equality arguments

Retain every triangle edge and the edges at selected vertices. The retained subgraph preserves every triangle count, and restoring all edges at a chosen center preserves that center's original degree. A cut can cover every vertex of retained degree at least three and one designated degree-two vertex when unsupported edges can only be incident to the designated vertex or one additional center. To cover a vertex means to give it two neighbors on the opposite side. [StarEarCut.lean](StarEarCut.lean) · [StarPalette.lean](StarPalette.lean)

In a failure, any covered set W representing all positive triangle counts has exactly one representative of every positive count and contains no zero. Its two omission shores have equal size and 2γ₂(G)+|W|=2n. Every outside vertex of degree at least two must touch both omission shores. Flipping connected components shows that each component of the retained graph contains an even number of representatives. Two cuts in subgraphs meeting at a single vertex can be aligned while keeping two crossing neighbors for that vertex if it has total degree at least three. [BalancedOmissions.lean](BalancedOmissions.lean) · [ComponentBalance.lean](ComponentBalance.lean) · [CutAtVertex.lean](CutAtVertex.lean)

## A limitation of simultaneous protection

The 14-vertex connected graph in [EarExample.lean](EarExample.lean) has triangle counts 8, 5, 6, 4, 11, 10, 7, 12, 17, 2, 3, 1, 1, 0 in vertex order. The sole zero is a leaf. The two ears 11 and 12 both lie on four-cycles and share anchor 10. A cut protecting both forces 9, 10 and 2 to have the same color. Vertex 9 then has only one crossing neighbor. Thus no cut protects both ears and every vertex of count at least two, even though all counts at least two are distinct. The six-vertex set {2,6,7,9,10,13} two-dominates this graph and the catalogue bound is seven.

The general odd-diversity zero case remains open in this proof. A proposed two-disjoint-path argument is recorded separately as an unverified continuation. [Linkage note](LINKAGE-NOTE.md) With degree-two zeros, a surviving configuration has disjoint zero/ear neighborhoods and, for each pair, at least one center lies on no four-cycle. With only zero leaves or isolates, the restrictions on repeated positive counts and their blocks still apply. The example demonstrates a genuine limitation on strengthening the cut argument in that latter case.

## Dependencies and replay

The 14 top-level Lean modules are listed in compilation order in the new-source manifest. The 24 files in `prior/` are byte-for-byte entries from the frozen even-diversity source archive, SHA-256 `f6d5b9a897857de8ee9a18878341a061236a31cbdfe72e35676687cda520ef00`. [Predecessor sources](PRIOR-SOURCES.sha256) · [Optional predecessor objects](CHECKED-OBJECTS.tsv) · [New sources](NEW-SOURCES.sha256) · [New objects](NEW-OBJECTS.sha256)

The proof reuses the compact positive-palette extension, the one-ear route and pinning lemmas, graph monotonicity and the low-support estimate. The prior normalization theorem replaced a putative witness by one with pruned edges. It does not give the original-degree or block conclusions proved here. Prior fixed-order leaf and positive-core arguments have additional order and triangle-diversity hypotheses. No exact #397c inequality or #299 seed estimate is assumed. The finite example uses the #398-style direct witness pattern already included in AllPairs384b. [Public result index](https://github.com/vjdad4m/maths/blob/main/README.md) · [Earlier one-ear source](https://github.com/vjdad4m/maths/blob/b33aad93ffcaab8f8c9e21a6fc56592675782f6f/graffiti-384b-one-ear/src/OneEarFinish384b.lean) · [Baseline declaration hashes](BASELINE-SOURCE-MAP.tsv) · [Baseline source links](BASELINE-UPSTREAM.tsv)

The entry point checks Lean 4.19.0 at commit `6caaee842e94`, Mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, source hashes, warnings as errors, and the axiom whitelist. Each new object is compared with its expected SHA-256. The cold replay rebuilds all bundled Lean modules from source. The optional checked replay authenticates each bundled predecessor's workspace object before compiling the extension.

~~~sh
export CROSSFOUR_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin
export CROSSFOUR_MATHLIB=/absolute/path/to/built/mathlib4
python3 -B replay.py --cold
~~~

For checked mode run `python3 -B replay.py --checked /absolute/path/to/shared/workspace`.

## External proof search

The search in [search.py](search.py) enumerates connected supported cores of minimum degree at least two, then filters for an even number of positive types, at least one ear and distinct counts above one. At orders five through nine there were 593 candidate nonadjacent pairs of vertices of count at least two for attachment of a new degree-two zero. Every pair permitted a cut covering that zero, all rich vertices and some ear. The count sums over graphs and pairs before testing colors. Coverage stops at core order nine; the search did not enumerate all original graphs. The scripts and transcripts are provided separately from the Lean proof. [Diagnostic output](search.log) · [Relaxed search](relaxed.log) · [Ear-example search](ear_fixture_search.py) · [Ear-example output](ear_fixture.log)

~~~sh
python3 search.py /absolute/path/to/geng 5 6 7 8 9
python3 search.py /absolute/path/to/geng 5 6 7 8 --relax
python3 ear_fixture_search.py /absolute/path/to/geng
~~~

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
