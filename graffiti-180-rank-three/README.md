# Graffiti.pc 180 at higher bipartization deficit

The ordinary conjecture is `1+α(G)+maxᵣ E(r)≤L_s(G)+b(G)` for every finite connected simple graph of order at least two. Here `E(r)` includes the root, and `b(G)` is the largest order of an induced bipartite subgraph. Write `k=n-b(G)` for the minimum size of an odd-cycle vertex transversal. The general conjecture and the unrestricted `k=3` case remain unresolved here.

## Ordinary theorem

For every nontrivial connected graph, **Graffiti.pc 180 holds if `k≤δ₂`**, where `δ₂` is the second-smallest degree, counting multiplicity. It also holds if any root maximizing the even count has `deg(r)+δ₂≥k+2`. The first result covers every graph with `k≤3` and `δ₂≥3`. Both theorems allow cut vertices.

One can also see the first criterion directly from the published inequalities. At a failing root put `e=E(r)` and `L=L_s(G)`. Then `L+b≤α+e`. The #177 bound `2α+δ₂≤L+b` gives `α+δ₂≤e`. The parity-tree bound `2e+1≤n+L` from #169 now gives `b+δ₂+1≤n`, so failure requires `k≥δ₂+1`.

More generally, suppose the ordinary inequality fails at a particular root `r`. Put `Q={v:d(v,r) is odd}`. For every connected nonempty set `C` of even vertices,

```
|N(C) ∩ Q| ≤ |C| + k − δ₂.
```

For example, if `k=3` and `δ₂=2`, each even vertex has at most two odd neighbors. Two adjacent even vertices with two odd neighbors each must share one. The proof applies the published #177 bound and the incident-support leaf inequality to `Q∪C`, then bounds its component count by contracting the connected part containing `C` and its odd neighbors. These conclusions concern failure of the ordinary inequality at `r`. The rooted marking on a block obtained by splitting at cut vertices has different hypotheses.

The source files are `SupportRank180.lean` and `ConnectedSupport180.lean`. Main declarations are `conjecture180_of_second_degree`, `conjecture180_of_root_degree`, and `odd_neighborhood_obstruction` in `Minimal180.HigherRank`.

## Exact shortest-path tree test

Fix a root `r` with at least two neighbors, a distance parity class `P`, and an independent set `A`. Set `X=A∪P`, `D=X ∖ (A∩P)`. The eligible set `U` is `X` if `r∈A∩P`, and `X ∖ {r}` otherwise. A tree proves this marking when

```
1 + |A| + |P| ≤ |U ∩ leaves(T)| + b(G).
```

A predecessor of `x` is a neighbor one distance level nearer the root. Let `E_D` contain each nonroot `x∈D` with a predecessor outside `D`. For `x∈E_D` call only its predecessors outside `D` allowed. All predecessors are allowed for other vertices. For `B⊆X ∖ {r}`, let `N_+(B)` contain the nonroot vertices with an allowed predecessor in `B`. Put

```
s = 1[r ∈ D] + 1[r ∈ X]·max(deg(r)−2, 0) + |E_D|.
```

Some spanning tree preserving all distances to `r` proves the marking **if and only if** there is such a set `B` with

```
k + |B| ≤ s + |N_+(B)|.
```

It suffices to examine `|B|≤max(k-s,0)`. If the marks differ, `s≥1`. In particular, at `k≤3`, checking the empty set, single vertices and pairs is exact for the shortest-path-tree question. Failure of that test leaves spanning trees with different distances available.

The proof counts components of the tree induced on `D` by their first parent edge entering `D`. At a nonroot center each child after the first contributes a unit of degree excess. For a fixed set of centers the choice of parent is independent for each child. A child contributes two units when its chosen parent belongs to the center set and its parent edge enters `D`. Maximizing admits the entry-priority convention above. For the size bound, any family covering `t` more elements than it has sets admits a subfamily of at most `t` sets with the same threshold.

The source files are `ParentBudget180`, `ParentFiber180`, `LayerScore180`, `BreadthIdentity180`, `BreadthScore180`, `AdmissibleLayers180`, `SmallCover180`, `BoundedCenters180`, and `TwoCenters180` (all `.lean`). Main declarations are `breadth_iff`, `small_layer_iff`, and `rank_three_breadth_iff`.

## Shape of a failed block

For any failed rooted marking with a root of degree at least two, take a set `B⊆X ∖ {r}` and let `N(B)` be all its outward neighbors, with no entry restriction. Then

```
1 + 1[r ∈ X]·max(deg(r)−2, 0) + |N(B)| < k + |B|.
```

At deficit at most three, every marked nonroot vertex has at most two outward neighbors. Call a marked nonroot vertex with two outward neighbors a fork. The successor pairs of all forks intersect pairwise, and all forks occur at one distance from the root. Their pairs either contain a common successor or consist of all three pairs on a three-vertex set. Multiplicity of the pairs is allowed. An empty fork family satisfies the first alternative vacuously.

Non-distance-preserving trees give two further restrictions. At depth at least three, two distinct forks whose distinct successor pairs meet have the same unique predecessor. Consequently the three-pair alternative cannot occur at depth at least three outside the chosen parity class. At arbitrary rank, let `H` consist of edges between opposite parity classes. For a set `C⊆X` whose members are each at graph distance at least three from the root and pairwise at distance at least three,

```
1 + ∑_{v ∈ C} max(deg_H(v)−2, 0) < k.
```

The last result reserves the entire vertical star at every such center in one spanning tree while keeping the root internal. It counts all vertical neighbors, including inward neighbors.

The published rank-two assembly gives an induced biconnected block with a genuine failed marking in any hypothetical ordinary counterexample. The new `rank_three_residual` theorem shows that a counterexample of global deficit at most three would have an induced block of **exactly** deficit three satisfying the fork profile and failing every center test at that same marking. This uses monotonicity of the transversal number under graph embeddings.

The source files are `OutwardRank180`, `IntersectingPairs180`, `ForkPattern180`, `ForkTree180`, `DeepFork180`, `DeepTriangle180`, `Packing180`, and `RankThreeResidual180`.

## Seven-vertex obstruction to requiring an internal root

Keep all edges of the clique on `0,1,2,3,4`. Add `5` adjacent only to `0,1`, and `6` adjacent only to `2,3`. The graph is biconnected. Its bipartite order is four. Its unique maximum independent set is `{4,5,6}`, and its only maximizing even roots are `5,6`, each with even count four.

With root `5` the even vertices are `{2,3,4,5}`. The eligible set is `{2,3,4,5,6}`. If `5` is internal in a spanning tree, at least one further eligible vertex is internal. If `6` is a leaf, its neighbor `2` or `3` is internal. Thus at most three eligible leaves are possible. A shortest-path tree attains three. The tree with edges `2–0, 2–1, 2–3, 2–4, 2–6, 0–5` has four eligible leaves, including `5`, and five total leaves. The other maximizing root has the symmetric obstruction. Lean checks both roots and all maximum independent sets.

The rooted inequality for this marking requires four eligible leaves and holds with equality for every maximizing choice. Every witnessing tree makes the chosen root a leaf. This refutes the requirement that an internal-root tree suffice at deficit three, even after choosing among the maximizing roots and independent sets. The graph satisfies ordinary #180. No claim of minimum order is made.

The source files are `SevenData180`, `SevenObstruction180`, and `SevenMaximizers180`. These three modules need only `ParentFiber180` among the other new source files. The main declarations are `Minimal180.HigherRank.Seven.internal_root_obstruction` and `Minimal180.HigherRank.Seven.all_maximizing_markings`.

## Replay and provenance

The package contains the exact 97 published dependency sources. The paths and Git blob IDs at repository commit `a5807be3c5e58d04f3a972d3fe2bc58a96499447` are recorded in `published-blobs.txt`. This includes the earlier rank-two assembly, Graffiti.pc #177 and #169, the parity and leaf definitions, and the block, cut, and tree lemmas. The module list selects a replay target for each new source. [Published repository at the pinned revision](https://github.com/vjdad4m/maths/tree/a5807be3c5e58d04f3a972d3fe2bc58a96499447)

Use Lean 4.19.0 and a built Mathlib checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From the extracted package run

```sh
LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin \
MATHLIB_DIR=/absolute/path/to/mathlib4 bash graffiti-180-rank-three/verify.sh
```

The script creates a fresh object directory, checks the source digests, recompiles all project modules with warnings as errors, and independently replays the declarations of each new module with `Lean.Environment.replay`. It audits the printed axiom reports. The finite example uses kernel reduction through ordinary `decide`. The exploratory graph calculation is unnecessary for the proof or replay.

Both clean source runs recompiled 97 public modules and accepted 229 new declarations across 22 new modules. All 52 printed axiom reports list exactly `propext`, `Classical.choice`, and `Quot.sound`. The logs in `StrictReplay.log` and `ExtractedReplay.log` are byte-identical.
