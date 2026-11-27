# Graffiti.pc 180 on graphs of bipartization deficit at most two

For every finite simple connected graph G of order at least two, if deleting at most two vertices makes G bipartite, then

$$
1+\alpha(G)+\max_r E_G(r) \le L_s(G)+b(G).
$$

Here b is the maximum order of an induced bipartite subgraph, Lₛ is the maximum number of degree-one vertices in a spanning tree, and E counts all vertices at even shortest-path distance, including the root. The hypothesis is equivalent to |V(G)|−b(G)≤2. The formal theorem is `Minimal180.RootEar.conjecture180_deficit_two` in `RankTwoAssembly180.lean`.

The University of Houston–Downtown catalogue entry 180 lists the unrestricted conjecture as open. The statement and the four referenced definitions were checked against its public data on November 27, 2026. [Official catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Conjecture data](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) · [Definition data](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json)

## Rooted theorem and scope

In a biconnected graph G of order at least three and deficit at most two, choose any root r, either distance-parity class P, and any independent set A. Let U be A∪P with r erased unless it belongs to both sets. Let ℓ(G,U) be the maximum number of leaves in U among all spanning trees. Then

$$
                  1+|A|+|P|\le \ell(G,U)+b(G).
$$

`rank_two_block` in `RankTwoBlock180.lean` proves this for both single markings of a degree-two root as well as every other marking and degree. Biconnectivity is expressed by connectedness and preconnectedness after deleting each individual vertex. The proof assumes neither a chosen lower graph nor a chord nor a sparseness or enumeration hypothesis.

* `conjecture180_on_family` in `RankTwoAssembly180.lean` proves ordinary #180 for all finite cut-vertex assemblies of biconnected pieces of deficit at most two and nontrivial connected bipartite pieces. The number of pieces and their total deficit are unrestricted. The inductive class is `RankTwoFamily`. The proof of `conjecture180_deficit_two` constructs such an assembly for every nontrivial connected graph of global deficit at most two.
* `rank_two_gain` gives strict gain in the unrestricted eligible-leaf optimum for every tight lower equality with a strict decrease of the bipartite order to an upper biconnected graph of deficit at most two. The marks and the parity class come from the upper graph.
* `counterexample_has_residual` in `ResidualBlock180.lean` shows that an ordinary #180 counterexample must contain an induced biconnected graph of order at least three, of deficit at least three, on which some rooted marking fails. The graph embedding preserves edges and nonedges. The induced graph is asserted to fail the rooted inequality. Ordinary #180 at unrestricted deficit remains open in this work.

## Proof

Write D for the vertices carrying exactly one mark, I for the vertices carrying both, and O for the vertices carrying neither. Assume that a rooted marking fails. The published deficit-one descent forces the root to have degree two and to belong to D. In every spanning tree that alternates the distance-parity marks and keeps the root internal, the induced forest on D has exactly |D|−1 edges, and every vertex of A∪P has tree degree at most two.

1. **Pruning at a root neighbor.** Every spanning tree with internal root has at most |I|+2 leaves, even after adding the number of internal vertices in O to the count. Keep only the edge to r at a neighbor u. The resulting graph is connected, u is pendant, and r is internal in every spanning tree. If |I| were zero, the pruned graph would have maximum degree at most two by the published degree-to-leaves bound. Its pendant vertex and the degree sum force it to be a path. This colors G−u, contradicting the published rooted deficit-one theorem. Thus I is nonempty.
2. **The root has two disagreement neighbors.** Prescribing any shortest-path predecessor gives a parity tree containing the root star. Counting its parent edges on D proves that all shortest-path predecessors of vertices in D stay in D. Each marked nonroot vertex has at most one outward neighbor. If one root neighbor were outside D, the disagreements beyond the root would form a single chain starting at the other neighbor t. The weighted #177 bound forces the chain to continue past t. Its second edge is a bridge in the alternating graph. A tree exchange, with both root edges retained, forces O to be independent. Flipping the distance coloring across that bridge gives a coloring of G−t.
3. **The exchange when both root neighbors are in D.** A shortest path to any vertex in I must first leave D through a vertex w in O. Re-root a reference parity tree at the vertex t in D directly preceding w. The |D|−1 edge count keeps every noninitial parent in D. If a,b in O formed an edge, a spanning-tree extension would retain the reference edges on D, the attachment tw, and ab, with a noninitial terminal of D still a leaf. Both root edges survive. Counting tree edges incident to the independent set I then gives |V|−1+ℓ(G,U)≥2|I|+|D|+2. Together with b(G)≥|V|−2, that gives the required bound. Hence O is independent.
4. **The two chains cannot merge.** Two distinct disagreements at the same positive depth exhaust that entire distance layer, and all shallower vertices lie in D. This follows by induction using predecessor closure and uniqueness of outward neighbors away from r. If a disagreement had two predecessors, those two vertices would exhaust the preceding layer and have the same unique outward neighbor. A singleton positive layer in a biconnected graph has no vertex beyond it. Every vertex would belong to D, contradicting the existence of I. Consequently every nonroot disagreement has a unique predecessor. In the whole alternating graph, the internal edges on D are exactly its predecessor edges. The |D|−1 edge count forces every one of those edges in every root-internal parity tree. Each such edge avoiding the root is a bridge in the alternating graph.
5. **One vertex meets every odd cycle.** Choose a geodesic from r to a deepest disagreement. Every horizontal edge meets the positive-depth portion of this path. Indeed I and O are independent, so some endpoint is a disagreement. If that endpoint differs from the path vertex at its depth, the two disagreements exhaust the layer. Let t be the first path vertex after r. For a one-edge path every horizontal edge meets t, and the distance parity colors G−t. For a longer path, remove its second edge in the alternating graph. The published separation lemma puts each later path vertex on the far side while all other vertices at its depth stay on the root side. Flip distance parity on the far side. Every surviving horizontal edge is now properly colored and every surviving vertical edge stays properly colored. Thus G−t is bipartite. This contradicts the deficit-one theorem and proves the rooted result.

## Source map

The declarations named above are in the namespace `Minimal180.RootEar`. These are the new modules in import order.

| Modules | Checked contribution |
|---|---|
| PortPrune180, PortColor180 | Root-internal leaf budget, pruning, and the disjoint-mark case |
| PortLayers180, SingleArm180 | Closure under every predecessor, nonincreasing layer width, and the one-arm structure |
| ArmTree180, ArmOutside180, SecondEdge180, TwoPorts180 | Prescribed-tree extension, independence of O on one arm, second bridge, and exclusion of a root neighbor outside D |
| TreeOrientation180, BothArmTree180, OutsideIndependent180 | Re-rooted exchange and independence of O in the residual two-arm case |
| DualLayer180, VerticalForest180 | Exhaustion of a layer by two disagreements, exclusion of mergers, and forced vertical edges |
| LongArm180, LongSeparation180, RankTwoBlock180 | A longest arm hits every horizontal edge, separation, and the general rooted deficit-two theorem |
| RankTwoAssembly180, ResidualBlock180 | Ordinary #180 on the stated graph classes, strict transition gain, and localization of any ordinary counterexample |

`foundation.txt` and `published-blobs.txt` give the replay order, repository paths and Git blob IDs of all 79 imported graph modules. Each pinned dependency matches the public repository tree at [23341cea1845e9d71e4ec5a58b0b908e47cdf86b](https://github.com/vjdad4m/maths/tree/23341cea1845e9d71e4ec5a58b0b908e47cdf86b). In particular the proof reuses the published deficit-one descent and the induced-bipartite, distance-parity, tree and cut-assembly tools it imports.

## Replay

Use Lean 4.19.0 and a built checkout of Mathlib 4.19.0 at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Run from the repository root.

```sh
LEAN_BIN=/absolute/path/to/lean-4.19.0/bin MATHLIB_DIR=/absolute/path/to/mathlib4 bash graffiti-180-rank-two/verify.sh
```

The verifier checks the manifests, strictly recompiles the pinned dependency closure into an empty object directory, and compiles each of the 18 new modules with warnings as errors. It then kernel-replays every new declaration against that module's imports. The named theorem must be absent before replay and present afterward. Replay rejects new axiom, unsafe, and partial declarations. Two fresh-object-directory replays produced byte-identical logs. Each recompiled 79 pinned imports and 18 new modules, kernel-replayed 191 new declarations, and checked 42 printed axiom reports. Every report lists exactly `propext`, `Classical.choice` and `Quot.sound`. The frozen-source run is recorded in `StrictReplay.log`. No C++ search or graph enumeration is used.
