# Graffiti.pc #384b for 29 triangle-count types, 28 nonleaves and no five-clique

**Every five-clique-free finite simple graph with exactly 29 vertex triangle-count types and exactly 28 vertices of degree at least two satisfies the catalogue inequality.** For this profile the right-hand side is $|V(G)|-15$. The Lean theorem works without an extra connectivity hypothesis. The set of types includes zero whenever a vertex realizes it. The general conjecture and the same profile with a five-clique remain outside this result. [Original-graph theorem](OriginalClique28.lean)

## The forced cut

Assume the inequality fails. The previous package reduces to a 28-vertex core $J$ with positive pairwise distinct triangle counts and $\gamma_2(J)\ge14$. Its degree-two vertex $e$ has neighbors $a,b$, and there is a fourth vertex $s$ adjacent to both. Thus $P=\{a,b\}$ and $R=\{e,s\}$ form the sides of a four-cycle. Two cubic vertices $u,v$ have triangle counts two and three. Their open neighborhoods together contain at most six vertices. The preceding reduction also proves these neighborhoods disjoint. [Original-graph reduction](CliqueForced28.lean) · [Frozen predecessor](https://github.com/vjdad4m/maths/tree/b7fa99b6bf51e71b79fd16bca72d1bf8e7abaa76/graffiti-384b-high-square-disjoint)

Let $x$ be outside the square and outside both cubic neighborhoods. Suppose $x$ sees at most one square vertex. If its open neighborhood contained a four-cycle, we could pin that cycle and the ear square with compatible colors, since they intersect in at most one vertex. The omitted vertex $x$ would see two pins of each color. Every unpinned vertex still has degree at least three after removing $x$. Indeed, $e$ is pinned, and $u,v$ miss $x$. Every other vertex has degree at least four because the positive counts one through three are already taken. A maximum cut extending the pins would then yield two 2-dominating sets partitioning the other 27 vertices, one of size at most 13. Consequently the link of $x$ contains no four-cycle, including a four-cycle with chords. [Protected-cut proof](FrameLinks28.lean)

For a four-cycle-free graph on $m$ vertices, choose a vertex of maximum degree $d$. Its neighbors induce a matching and isolated vertices. Every vertex outside the closed neighborhood sees at most one of those neighbors. If $E(m)$ bounds the edge count, the handshake identity and this decomposition give the two bounds
\[
\left\lfloor\frac{md}{2}\right\rfloor,\qquad
m-1+\left\lfloor\frac d2\right\rfloor+E(m-1-d).
\]
For $m=0,\ldots,10$ the verified upper bounds are $0,0,1,3,4,6,7,10,12,14,17$. These suffice because the triangle count at $x$ equals the number of edges in its link. [Recurrence and integer table](SparseLink28.lean)

## The three samples

Let $W$ be the 24 vertices outside the ear square. In each trial, retain the pins and the sample from $W$, then add every omitted vertex with fewer than two retained neighbors. The square vertices are already protected in every trial. If $\gamma_2(J)\ge14$, each sample needs at least the indicated number of additions.

| Retained pins | Sample size from $W$ | Minimum additions | Weight |
|---|---:|---:|---:|
| $a,b$ | 8 | 4 | 6 |
| $a,b,s$ | 7 | 4 | 4 |
| $e,s$ | 9 | 3 | 1 |

The weighted number of additions must be at least $24\binom{24}{8}+16\binom{24}{7}+3\binom{24}{9}=27{,}111{,}480$. For each exterior vertex the proof simultaneously counts deficiencies in all three trials, using its actual numbers of neighbors in $W$, in $P$, and at $s$. The 24 distinct exterior triangle counts have rank lower bounds $2,\ldots,25$. Each rank receives a verified upper bound using the five-clique-free neighborhood estimate and the four-cycle-free estimate where applicable. The rank bounds sum to 22,577,006. Each of at most six vertices in the cubic neighborhoods may add 636,922. The resulting total of **26,398,538** falls short by **712,942**. This argument covers zero, singleton and higher intersections of $N(s)$ with the private triangle of the score-three cubic. [Rank inequalities](WeightedRows28.lean) · [Graph coverage and weighted totals](ThreeTrials28.lean)

The core construction induces on the nonleaves and applies the frozen edge-trimming definition. In a hypothetical failure every core vertex has positive count, so the trim retains precisely the edges lying in triangles. The equivalence between a five-clique in the trimmed core and a five-clique in the original graph is proved for every finite simple graph. [Clique equivalence](OriginalClique28.lean)

## Sources and verification

The six linked Lean files are the entire new source set. The package reuses the exact definitions of two-domination, triangle counts, types and nonleaves in the 303 predecessor modules. The key reused arguments are the square alignment and cut in EarFrame33.merge_shared, the sparse crossing-edge bound in Four28.sparse_cross, the sample completion and count in Thin28.budget and HighSquare28.bill_bound, and the original-graph reduction in HighSquare28.disjoint_frontier. The earlier one-common-neighbor and alternate-pin estimates establish the predecessor structure. Their numerical thresholds alone do not give the bound here. [Public checked-result index](https://github.com/vjdad4m/maths/blob/main/README.md)

The exploratory optimization suggested the integer weights. All coverage and all reported graph and arithmetic inequalities are proved in Lean. The logs record two checked-mode executions in separate empty build directories. Each authenticated 303 predecessor source and object hashes, freshly compiled six modules, matched six resulting object hashes, and checked 11 axiom reports. The permitted axioms are propext, Classical.choice and Quot.sound. The replay scans every included source for proof placeholders, custom axiom declarations and native_decide. [First replay](StrictSparse.first.log) · [Second replay](StrictSparse.log) · [Fresh source hashes](NEW-SOURCES.sha256) · [Fresh object hashes](NEW-OBJECTS.sha256) · [Predecessor sources](PRIOR-SOURCES.sha256) · [Predecessor objects](CHECKED-OBJECTS.tsv)

The replay pins Lean 4.19.0 commit 6caaee842e94 and Mathlib v4.19.0 commit c44e0c8ee63ca166450922a373c7409c5d26b00b. It uses a single Lean thread, synchronous elaboration and warnings as errors. Set CROSSFOUR_LEAN_BIN and CROSSFOUR_MATHLIB to compatible local paths. The cold option recompiles all predecessor modules from the bundled source archives. The recorded runs used checked mode. [Replay entry point](replay.py)

~~~sh
python3 replay.py --checked /absolute/path/to/shared/workspace
python3 replay.py --cold
~~~
