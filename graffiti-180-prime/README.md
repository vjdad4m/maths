# Graffiti.pc #180 on prime graphs

The ordinary inequality for every finite simple connected graph of order at least two is equivalent to two rooted tests on **connected nonbipartite prime graphs of order at least three**. Both tests use only the prime graph. A root is tested only when it lies on no dominating edge. The equivalence is proved by `universal_iff_nonbipartite_prime_tests` in `PrimeObstruction180.lean`. The two prime tests remain open in general.

Here a module is a set of vertices whose members have the same neighbors outside that set. A graph is prime when its only modules are its empty set, singletons and whole vertex set. An edge is dominating when each vertex outside the edge is adjacent to at least one endpoint. Ordinary #180 is
$$
1+\alpha(G)+\max_r E(r)\le L_s(G)+b(G).
$$
The even-distance count includes the root. The leaf number counts degree-one vertices in a spanning tree. The invariant $b(G)$ is the largest order of an induced bipartite subgraph.

## The two tests

Fix a prime graph and root $r$ satisfying the hypotheses above. For a parity $p$, let $P$ be all vertices at shortest-path distance of parity $p$ from $r$. Let $I$ be an independent set. Put $U=(I\cup P)\setminus\{r\}$, adding $r$ back exactly when $r\in I\cap P$. Write $W(U)$ for the maximum, over all spanning trees, of the number of leaves in $U$.

1. For every $p,I$, find a vertex set $Z\supseteq I\cap P$ inducing a bipartite graph for which $1+|I|+|P|\le W(U)+|Z|$.
2. For odd $p$ and every $I$ containing $r$, find a vertex set $Z\supseteq\{r\}\cup(I\cap P)$ inducing a bipartite graph for which $1+|I|+|P|\le W(U)+|Z|+\mathbf1_{N(r)\cap Z=\varnothing}$.

Each inequality uses the order of its own witness. Different roots, markings and tests may use different witnesses. The prime reduction includes prime graphs with cut vertices. A separate equivalence in `PinnedEquivalent180.lean` uses the first test on all biconnected blocks. Combining both restrictions would require another argument.

## Proof of the reduction

For a marked independent subset $D\subseteq I\cap P$, attach $n$ extra independent copies to each vertex of $D$, with $n=|V(G)|$. An optimal induced bipartite set in the expansion projects to a bipartite set containing $D$. Projection preserves the relevant parity marking and bounds the number of eligible leaves. The existing rooted-to-ordinary realization then proves that failure of the first test with required set $D$ produces a genuine ordinary counterexample of order at most $4n(1+|D|)-1$. This argument establishes necessity of requiring the bipartite witness to contain the doubly marked vertices.

Consider a failing first test minimal under taking proper connected induced subgraphs. Deleting an unpinned nonroot vertex of a nonsingleton module preserves failure. A pinned nonroot vertex can also be deleted if it has a pinned false twin. It follows that each proper nontrivial module contains the root and has exactly two vertices. If the two are nonadjacent, the off-root vertex must belong to the independent marking and have even distance from the root. The root can then be added to the marking, and the resulting pinned false twins permit deletion. Hence any remaining pair consists of adjacent true twins, the parity is odd and the off-root twin belongs to the marking.

Keeping the off-root twin gives a smaller prime quotient. In a bipartite witness containing both adjacent twins, no common neighbor can occur. Conversely, after retaining one twin, the second can be added precisely when the retained one has no neighbor in the witness. Together with the exact eligible-leaf formula for the substitution, this gives exactly test 2 on the quotient. Strong induction proves sufficiency of the two tests. Both tests hold on bipartite graphs by taking all vertices for the witness. The original rooted dominating-edge theorem and the forcing construction remove the indicated roots.

A failed second test at a qualifying root of an $n$-vertex graph produces an ordinary #180 counterexample of order at most $4(n+1)(|I\cap P|+2)-1$. The ordinary counterexample supplied by either realization may be larger than the graph of the failed test.

## Quotients with arbitrary nonempty bags

In a substitution $H\to G$, each quotient vertex indexes a nonempty bag. Distinct bags have all possible edges between them exactly when their quotient vertices are adjacent. For any vertex set $U\subseteq V(H)$, let $F$ consist of those quotient vertices whose entire bag lies in $U$. When $G$ is connected, has order at least three and has no universal vertex, Lean verifies
$$
W_H(U)+|F|=|U|+W_G(F).
$$
The internal edge sets of the bags are arbitrary.

Every independent set of vertices of degree at most three fits simultaneously in a maximum induced bipartite subgraph. The proof inserts a missing marked vertex into a color class where it has at most one neighbor and removes that neighbor if needed. Independence preserves all previously required vertices. As a result, the rooted bound $1+|I|+|P|\le W(U)+b(G)$ for all independent $I$ at a given root and parity lifts to $H$ if every quotient vertex with a nonclique bag has degree at most three.

This gives a full ordinary #180 theorem for arbitrary substitutions of the earlier rank-two cut-assembly family under that degree condition. In particular the quotient can be nonbipartite and become bipartite after deleting at most two vertices. There is no corresponding deficit bound on $H$. For subcubic quotients every bag is unrestricted. On a subcubic graph, the usual rooted inequality at both parities already implies both new tests at that root.

## Source map

| Files | Checked results |
|---|---|
| `BagCost180`, `RetainBags180` | Exact eligible-leaf cost and comparison after retaining a member of each bag |
| `ColorRepair180`, `ModuleQuotient180`, `PrimeCubic180` | Simultaneous degree-three color repair, strict quotient descent and the prime subcubic block restriction |
| `PruneMarks180`, `ModuleShape180` | Minimal unpinned failures and the markings on their proper modules |
| `ForceColor180`, `ForceMarks180`, `PinnedEquivalent180` | Independent-copy construction, counterexample order bound and equivalence with pinned tests on blocks |
| `PinnedTools180`, `PinnedDelete180`, `PinnedPrime180` | Dominating edges, vertex deletion and the restriction to root pairs |
| `PrimeQuotient180`, `RootPairParity180`, `PrimeChart180` | Prime quotient, exclusion of a nonadjacent root pair and the adjacent-twin construction |
| `TrueChart180`, `RootBonus180` | Exact changes in parity, eligible leaves and the bipartite witness for an adjacent root twin |
| `PrimeTests180`, `PrimeObstruction180` | Equivalence on prime graphs, removal of the bipartite case and both failure realizations |
| `LowMark180` | Cut-assembly substitution corollary and sufficient low-degree marking conditions |

## Strict replay

Use Lean 4.19.0 and a built Mathlib checkout at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From the extracted package run

```bash
sha256sum --check --status bundle.sha256
MATHLIB_DIR=/absolute/path/to/mathlib LEAN_BIN=/absolute/path/to/lean-4.19.0/bin bash verify.sh
```

The script builds all 115 repository dependencies from the pinned repository sources, then compiles the 21 new modules with warnings as errors. It replays all declarations in each new module in a freshly imported Lean kernel environment, rejects new axioms and unsafe or partial declarations, and checks every printed axiom report against `propext`, `Classical.choice` and `Quot.sound`. `FinalExtractedReplay.log` records a clean build. The 115 dependencies match Git blobs in `published-blobs.txt` at the pinned repository commit. The order of compilation and module targets are in `foundation.txt` and `modules.txt`. Source digests are included.

The earlier repository supplies #169, #177, #318 and the #180 rooted realization, assembly, deletion and substitution packages. [Pinned public repository](https://github.com/vjdad4m/maths/tree/bc5b333b70aeb89803bec2b860e251360fc02a15)

## Replay from GitHub

From the repository root, run `bash graffiti-180-prime/verify.sh` with
`MATHLIB_DIR` set to the built, pinned Mathlib checkout and, if needed,
`LEAN_BIN` set to the Lean 4.19.0 binary directory. The script stages the
115 already-published source dependencies from the checkout, verifies their
Git blob and SHA-256 hashes, and rebuilds the package. The included log is
from the agent's clean replay of the same source files.
