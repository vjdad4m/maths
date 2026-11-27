# Root deletion and the low-degree branch of Graffiti.pc 180

For a connected simple graph of order at least two, the ordinary inequality is
`1 + α(G) + max_r E(r) ≤ L(G) + b(G)`. Here E(r) counts vertices at even shortest-path distance, including r. L is the maximum number of degree-one vertices in a spanning tree. The order of a largest induced bipartite subgraph is b. Write k = n − b and δ₂ for the second-smallest degree, counting multiplicities.

## An exact root-deletion test at every deficit

Add a root r to a connected graph G on at least three vertices. Its neighbor set N has at least two vertices. For every old vertex v, its new distance to r is

```
1 + min_{x∈N} d_G(v,x).
```

Fix upper distance parity p (zero for even, one for odd). Let P consist of the old vertices whose minimum distance to N has parity 1−p. For an old independent set A, let a be 0 or 1, recording whether the new root belongs to the chosen independent set. The choice a=1 requires A disjoint from N. Put U=A∪P and e=a(1−p). Write W(G,S) for the largest number of vertices in S which are leaves of one spanning tree of G.

The restored bipartite order b′ equals b(G)+1 if some maximum induced bipartite subgraph of G has a two-coloring with one color class disjoint from N. Otherwise b′=b(G). Set

```
t = max(0, 1 + |A| + a + |P| + (1−p) − b′).
```

The rooted inequality for this marking holds precisely when at least one of these two tests succeeds.

1. Some S⊆U has |S|≥t, every connected component of G−S meets N, and each vertex of S outside N has a neighbor in G−S.
2. Some x∈N has W(G,U∖{x})+e≥t.

The first test corresponds to taking the full root star, the second to attaching the root as a leaf. All quantities and sets in the tests, including the threshold, are computed in G. The entire upper local bound holds exactly when these tests cover every admissible A and a. This result does not require that the nearest-port parity agree with distance parity from any fixed old vertex. The checked declarations are `deleted_root_iff`, `rooted_old_tests`, `con_lift_iff`, and `apex_dist`.

The conditional transfer at an individual x∈N uses the ordinary old parity class Q at x for parity 1−p. If the smaller rooted inequality holds for A and Q, the following inequality suffices for the restored one. Brackets denote indicator values.

```
b(G) + |P∖Q| + [a=1 or p=0] + [x∈A∩Q] ≤ b′ + |(Q∖P)∩A|.
```

For two ports x,y with d_G(x,y)≤2, define the directed sector S by d_G(v,x)=d_G(v,y)+1. Then P∖Q=S∖Q and Q∖P=S∩Q. In particular, if the upper deficit is three and the deletion has deficit at most two, the bipartite order is unchanged and the old rooted inequality is available from the published rank-two theorem. On failure at an even root, every orientation of such a nearby pair must satisfy |S∩Q∩A|≤|S∖Q| for Q the old odd vertices at the first port. See `transfer_at_port`, `pair_changes`, `rank_two_deletion`, and `rank_three_even_obstruction`.

## Ordinary failure when k≤δ₂+1

Take a root r at which the ordinary inequality fails. Let E and O denote its even and odd vertices. The crossing graph H retains precisely the original edges between E and O.

If k≤δ₂+1, failure forces k=δ₂+1, |E|=α+δ₂, L+n=2|E|+1, and O is independent in the original graph. Every spanning tree of H attains the unrestricted L. All its leaves are even, and each even vertex has tree degree at most two. Each odd vertex cuts H and has a child for which it is the sole shortest-path predecessor in G.

More generally, at arbitrary deficit, if a set S of odd vertices can be removed while H−S stays connected, then failure requires |S|+δ₂+1≤k. For any collection of odd levels, let X be their union and Y the union of their immediately following even levels. Failure requires |X|−|Y| < k−δ₂. Thus when k=3 and δ₂=2, one odd level wider than its successor at any maximizing root proves ordinary #180. This includes an odd final level. See `saturated_tree`, `removable_odds_budget`, `widths_budget`, and `conjecture180_of_layer`.

At arbitrary deficit, let S be the odd vertices of degree one in the crossing graph H. At every failed root and for every even vertex a, |S|+max(0,deg_H(a)−2) < k−δ₂. Consequently two odd degree-one vertices in H at a maximizing root settle ordinary #180 for all k≤3, including δ₂=1. The two vertices need only be leaves of H. See `pendant_star` and `conjecture180_two_odd_pendants`.

### Reconnecting an odd cut with an even edge

Under the same borderline hypothesis, every spanning tree T of the original graph satisfies

```
(number of odd leaves of T) + ∑_{v∈E} max(0,deg_T(v)−2)
    ≤ (number of even–even edges of T).
```

For any connected spanning subgraph F of G, suppose F−S is connected for a set S of odd vertices. For any even vertex a, |S|+max(0,deg_F(a)−2) cannot exceed the number of even–even edges of F. A spanning tree can simultaneously retain all of S as leaves and every edge incident to a. The previous inequality applied to that tree proves the bound. For arbitrary deficit, if the odd vertices are independent in F, failure requires |S|+max(0,deg_F(a)−2) < k−δ₂+h, where h is the number of even–even edges of F. See `horizontal_identity`, `charge_horizontal`, `core_star_charge`, and `general_star_budget`.

Consequently, if adding a single even–even edge ab to H reconnects H−v after deleting an odd vertex v, then each of a,b has exactly one neighbor in H. If either has at least two, the ordinary inequality holds at r. The theorem `conjecture180_reconnecting_chord` gives ordinary #180 for a maximizing root under this condition, k≤3 and δ₂≥2. If G−v is connected at a borderline failure, at least one horizontal even edge between distinct components of H−v must exist. Such an edge alone need not reconnect all components. The distinction is explicit in `odd_cut_bypass` and `borderline_odd_vertex`.

### Maximum independent sets and private successors

For any maximum independent set A, choose a private child f(q) for each q∈A∩O. Its only shortest-path predecessor is q. At a borderline failure every choice has one of two properties. Either two chosen children are adjacent, or one child has a deeper odd neighbor outside A.

The children are distinct, even, and outside A. If neither property held they could all join O∖A in an independent color class disjoint from A. Together the two color classes would have order α+|O|=n−δ₂, one more than b. This proves the obstruction for every maximizing A in the same original graph. The theorem `conjecture180_last_odd` proves ordinary #180 if a maximizing root admits a maximum independent set whose only odd member lies at maximum odd depth. The same theorem allows A to have no odd member. See also `companion_shortage`, `private_choices` and `private_conflict`.

## Source and replay

The general conjecture, the unrestricted deficit-three case, and the claim that one of the two old-graph tests always succeeds remain open in this work. All implications above are Lean theorems. No enumeration is used to establish them.

All new declarations are in namespace `Minimal180.PortParity`. The file `modules.txt` gives the order and a named kernel replay target per module. The archive contains the 98 sources in the exact transitive project import closure. Of these, 96 are pinned by Git blob ID to the public repository at commit `5ffbe8fe5e94511afb20e07b7e164e78aa02b942`. The two earlier local modules, `RootChoice180` and `SupportRank180`, are included with source SHA-256 hashes from their previous checked packages. These dependencies include the earlier maximum-leaf proof of #169, the #177 proof, the weighted core and full-star results, color extension, and the rank-two assembly. [Public source revision](https://github.com/vjdad4m/maths/tree/5ffbe8fe5e94511afb20e07b7e164e78aa02b942)

Use Lean 4.19.0 and a built Mathlib checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```sh
LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin \
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The script checks source digests, builds all project imports and new modules with warnings as errors in a fresh object directory, then independently replays the declarations of each new module with Lean’s kernel and audits all explicit axiom reports. The replay rejects new axioms, unsafe and partial declarations.

## Dependency map for independent checking

| Result | New modules, in dependency order |
| --- | --- |
| Exact deletion test on the smaller graph | NearestPort180, PortComponents180, PortRecurrence180, DeletedRoot180 |
| Signed change in distance parity and the rank-three sector test | NearestPort180, ParityBudget180, PairDistance180, RankThreePort180 |
| Saturation, odd cuts and layer widths | SaturatedParity180, OddCutBudget180, ParitySeam180, LayerCut180 |
| Reconnecting horizontal chord | HorizontalCost180, OneBypass180, RankThreeBypass180, following the preceding row |
| Private children of a maximum independent set | PrivateSuccessors180, LastOdd180, following RankThreeBypass180 |
| Arbitrary-deficit charge and the second-degree-one case | LowDegree180, following OneBypass180 |

The source closure contains all shared prerequisites for each group. The new modules total 161 replayed declarations and have 45 printed theorem axiom reports, each listing exactly `propext`, `Classical.choice`, and `Quot.sound`. The complete runs are recorded in `StrictReplay.log` and `FinalExtractedReplay.log`.
