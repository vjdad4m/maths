# Graffiti.pc 180 under vertex substitution and root deletion

Every nonempty graph substitution into a finite connected bipartite base of order at least two satisfies Graffiti.pc 180. A substitution replaces each base vertex with an arbitrary nonempty finite simple graph. Two distinct bags are completely joined when their base vertices are adjacent and have no edges between them otherwise. The theorem imposes no diameter or bipartization-deficit bound. It also proves the stronger rooted inequality for **every** root, **both** shortest-distance parities, and **every** independent marking. The unrestricted conjecture remains open.

For a connected simple graph H, write b(H) for its maximum induced bipartite order, α(H) for its independence number, L(H) for its maximum spanning-tree leaf count, and E(r) for its number of even-distance vertices, including r. The checked ordinary conclusion is

```
1 + α(H) + max_r E(r) ≤ L(H) + b(H).
```

## How the graph-wide condition makes the root-deletion tests pass

On the deleted side, G is connected and has at least three vertices. Restoring a root r adjacent exactly to a port set N of size at least two gives H. If H has the bipartite substitution above, the deleted-root disjunction holds for every legal marking and either parity. There is also a directly checkable sufficient condition on G. If some port y is adjacent to every vertex outside N, the disjunction holds for every marking and either parity. The latter hypothesis makes ry a dominating edge of H. The general rooted lemma needs only that r lies on a dominating edge.

Write A for an independent marking on G, a for the bit indicating whether r is also marked independent, and p for the parity requested in H (0 even, 1 odd). When a=1 the marking must avoid N. Let P consist of old vertices whose distance to the nearest port has parity 1−p. Put U=A∪P and

```
t = max(0, 1 + |A| + a + |P| + (1−p) − b(H)).
```

The old formula `restoredB G N` computes b(H) from G and N. Denote by C(U,t) the assertion that some S⊆U has |S|≥t, every component of G−S meets N, and every vertex in S either belongs to N or has a neighbor outside S. Write W_G(U) for the maximum number of leaves in U over all spanning trees of G.

The new exact normal form says that a legal marking succeeds precisely when C(U,t) holds or all of the following conditions hold together.

- The independent marking contains r and the requested parity is even.
- The threshold satisfies t=W_G(U)+1.
- For every nonnegative integer q, C(U,q) holds precisely when q≤W_G(U).

This is valid at every deficit, without a substitution hypothesis. When r receives the extra leaf credit, every port is outside U. Erasing any port therefore gives the same old score. When the credit vanishes, the port alternative implies C(U,t). In particular, the single core test characterizes the entire odd-parity inequality. These equivalences give a proof obligation on the smaller graph. They establish no unconditional odd-parity inequality on arbitrary graphs.

The exceptional case occurs. In every complete graph of order at least four, fix a root and mark just the root independent with even parity. Only the port alternative succeeds. At the same root mark a single old vertex independent and use odd parity. Only the core alternative succeeds. The theorem proves both exclusivities and ordinary #180 on that graph. The two markings have different parities. This example refutes a branch choice fixed before seeing the marking.

## Rooted transfer through general substitutions

Let f map each vertex of H to its base vertex in G. For every independent support I of G, assume that some maximum induced bipartite set contains all vertices of I whose fibers are noncliques. The witness can depend on I. This condition holds for every substitution of a bipartite base, and it holds over every base when all fibers are cliques.

For each r and each p, the rooted inequality on G at f(r),p then implies the rooted inequality on H at r,p. If f identifies two vertices, a failed upper inequality descends to the same parity on a strictly smaller base. An adjacent true twin can always be folded. For a nonadjacent false twin, the stated covering condition is equivalent to the original vertex lying in some maximum induced bipartite set. The transfer theorem supplies a sufficient hypothesis on a general base.

The representatives used for the spanning tree form an isometric copy of the base containing the actual root r. When the base has no universal vertex, every connected dominating core has at least two vertices. Its representatives form a connected dominating core upstairs, allowing every off-section eligible vertex to be a leaf. A second section, for the bipartite witness, may use a different representative in the root bag when p is odd and r lies outside the independent set. This distinction ensures that the extra doubly marked vertices can be added to that witness without a monochromatic edge. If the base has a universal vertex, every upper root is an endpoint of a dominating edge, which handles singleton cores.

The inductive family also permits any number of further covered substitutions and one-vertex sums. Its starting cases include the published rank-two assembly family and graphs in which each vertex lies on a dominating edge.

## Biconnected blocks of every deficit

For a connected base of order at least three, an upper vertex is a cut vertex precisely when it is alone in its bag and its base vertex is a cut vertex. This equivalence permits arbitrary edges inside the individual bags.

There is an explicit construction `growClique G c k` for every nontrivial connected bipartite G. It replaces c by a clique of order k+1. Its largest induced bipartite subgraph has order |V(G)|, so its deficit is exactly k. The original vertices retain their pairwise distances. Every original vertex outside the closed neighborhood of c retains its degree. If the base has order at least three and no cut vertex, the new graph has no cut vertex. It satisfies all the rooted bounds and ordinary #180. Taking an even cycle as base yields examples with degree-two vertices and large root distances at the same time as arbitrarily large deficit.

For the exact order calculation, one representative from each bag induces a bipartite graph of base order. Any bipartite witness uses at most two vertices of the enlarged clique. If it uses two, it omits every neighbor of that base vertex. At least one such neighbor exists and occupies a singleton bag. This offsets the second clique vertex.

## Source and replay map

All theorems below are in the namespace `Minimal180.Substitution`.

| Result | Source files and principal declaration |
| --- | --- |
| Endpoints of dominating edges, both parities | `CorePayment180`, `DominatingEdge180`, `DomRoot180`, declaration `dom_edge_rooted` |
| Isometric representatives, leaf lifting, bipartite witness and two compatible sections | `BagMetric180`, `BagLeaves180`, `BagColor180`, `BagSections180`, `BagTransfer180` |
| General transfer and strict descent | `Substitution180`, declarations `Bags.rooted`, `Bags.strictDescent`, `Bags.bipartiteRooted` |
| Ordinary #180, deletion tests and recursive assembly | `DeletionClass180`, declarations `bipartite_substitution_ordinary`, `bipartite_substitution_passes`, `port_dominates_passes`, `Family.ordinary` |
| Folding a true or covered false twin | `FoldTwin180`, declarations `twin_cover_iff`, `twin_descent`, `twin_passes` |
| Forced port alternative, complete-graph obstruction | `BranchChoice180`, declarations `port_only_rigid`, `complete_requires_both` |
| Marking-specific deletion normal form, odd parity | `CreditedPort180`, declarations `deleted_root_normal`, `odd_root_core_iff` |
| Exact order, explicit growth, cut vertices | `OneClique180`, `Inflate180`, `BagBlocks180`, declarations `Bags.oneCliqueOrder`, `Bags.delete_pre_iff`, `grow_blocks` |

The source closure contains 101 earlier modules. The Git-tree snapshot for `vjdad4m/maths` is `efe727941d90bb5ab2cf2a05f565581bbdab7985`. The file `published-blobs.txt` maps 97 exact source blobs to paths at this commit. They include `Short177`, `Proof318`, `Rooted180`, `Core180`, `Assembly180`, `RootChoice180`, and `RankTwoAssembly180`. Four exact imports come from the preceding frozen port-parity package, whose archive SHA-256 is `8bb9c199c95d463cc85dab2786abd254cc362a2797ad6a79d881c1259dd61b7e`. Their individual digests are in `prior-local.sha256`. They are `NearestPort180`, `PortComponents180`, `PortRecurrence180`, and `DeletedRoot180`. Every dependency is included under `foundation/`. [Repository snapshot](https://github.com/vjdad4m/maths/tree/efe727941d90bb5ab2cf2a05f565581bbdab7985)

Use Lean 4.19.0 and the built Mathlib 4.19.0 checkout pinned below. With the two environment variables pointing to those installations, the complete replay command is

```sh
LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin \
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The verifier checks source digests and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, compiles with warnings as errors into a newly created empty object directory, independently kernel-replays the 16 new modules, and audits the named theorem axiom reports. All 179 new declarations and 54 printed reports are accounted for. Every printed axiom report lists exactly `propext`, `Classical.choice`, and `Quot.sound`. The verifier rejects new unsafe, partial, or axiomatic declarations. The logs `StrictReplay.log` and `FinalExtractedReplay.log` give the results of the clean source run and the clean extracted-source run.
