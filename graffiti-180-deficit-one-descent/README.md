# Graffiti.pc 180 — the deficit-one cut branch

**The full tight, rooted-sparse horizontal cut-triangle transition cannot occur when the lower graph has bipartization deficit one.** The main theorem is `Minimal180.DescentOne.no_tight_cut_one` in `NoTightCut180.lean`. It applies at every chord depth. The intermediate theorem `deficit_one_cut_gain` proves the strict increase of the unrestricted eligible-leaf optimum under those hypotheses.

## Exact scopes

Write b(H) for the maximum order of an induced bipartite subgraph, and ℓ(H,U) for the maximum number of leaves in U among spanning trees of H. For root r and parity choice p, P is its distance-parity class. The independent mark is A. The eligible set U is A∪P with r erased unless r belongs to both marks.

* **Cut exclusion.** The input is precisely the published `Minimal180.CutGain.TightCut J S T x y w r p A`, together with b(J)+1=|V|. It requires a connected lower graph J of order at least four with a proper split into S and T meeting at w, the edges xw and wy, and no xy. The root lies on the named near side. The upper graph G=J+xy is biconnected and rooted-sparse, xy is horizontal, A is independent in G, b(J)=b(G)+1, and ℓ(J,U)+b(J)=1+|A|+|P|. The theorem contradicts this conjunction. It imposes no maximum-depth condition, search cutoff, additional leaf restrictions, or smaller-graph induction hypothesis.
* **General upper block.** For a finite biconnected G on at least three vertices with |V|≤b(G)+2, the rooted bound 1+|A|+|P|≤ℓ(G,U)+b(G) holds if r has degree at least three or r has the same membership in A and P. This covers both parity choices. The theorem `rank_two_root` requires no sparsity assumption, horizontal edge, or lower graph. For an actual rank-dropping transition with tight lower equality, `transition_gain` then gives strict eligible-leaf gain under the same root condition, including biconnected lower graphs and those without a common neighbor.
* **Remaining block cases.** At upper deficit two, any hypothetical rooted failure has degree exactly two at r and exactly one mark on r. When r belongs only to A, every independent subset of U must be smaller than A. When r belongs only to P, every independent subset of U avoiding all neighbors of r must be smaller than A. The proof gives necessary conditions for a failure. No example of one is known here.
* **Ordinary #180 for block assemblies.** The unweighted inequality 1+α(G)+maxᵥ E(v)≤Lₛ(G)+b(G) holds for every finite graph assembled along single cut vertices from the following pieces: connected bipartite graphs of order at least two, biconnected graphs of deficit at most one, and biconnected graphs of deficit at most two with minimum degree at least three. The block constructor uses order at least three, with a single edge already covered as a bipartite piece. There is no bound on the number of pieces or the total deficit of an assembly. The formal class and theorem are `BlockFamily` and `conjecture180_on_family`. For example, arbitrary such assemblies of complete graphs on four vertices, odd cycles and bipartite graphs fall in the class.

## Why the cut closes

Suppose first that gain fails. The published cut-chain theorem puts the mark disagreements D=(A∪P)∖(A∩P) on one descending chain, starting at a triangle tip t and attached to the unmarked seam w. Its other vertices have unique predecessors in the lower graph.

1. Let I=A∩P. Any edge with both endpoints completely unmarked can be preserved together with all chain edges and its attachment to w, while leaving the last disagreement a leaf. The upper graph stays connected after deletion of that last vertex, which permits the spanning-tree extension. Sum degrees over the independent set I. The preserved edges avoid I, and the last leaf supplies a further eligible leaf outside I. This exceeds the tight upper score by one. The completely unmarked vertices are therefore independent.
2. Keep just the edges that change distance parity in J. The first edge of the chain is a bridge in this graph. Otherwise a parity tree could omit that edge and keep the root internal, leaving t isolated in the forest on D. The deficit-one equality forces this forest to have |D|−1 edges. Beyond the bridge, every disagreement is separated from the root. Every other vertex at the same depth is still reachable from the root after the edge is removed. This last assertion follows by induction on depth and the unique outward edge at a chain predecessor.
3. Delete t and flip the distance-parity color off the root component of that edge-deleted graph. Surviving parity-changing edges stay properly colored. Every horizontal edge has a disagreement endpoint because both I and the completely unmarked set are independent. Its two endpoints are at the same depth on opposite sides of the flip. Thus J−t is bipartite of order |V|−1=b(J). The published rank-drop criterion makes t compulsory in every maximum bipartite witness of J, a contradiction.
4. Strict gain and the published deficit-one marking equivalence now force A=P and w∈A. The remaining equality is itself impossible. Take the two triangle spokes and a third lower edge at w. In the wing of the third edge, the port is compulsory in every maximum bipartite witness. Deleting that port leaves an odd obstruction. Some edge avoiding the port has both endpoints outside A. At least one endpoint lies outside the three chosen neighbors of w, by the split. A spanning tree can retain the three spokes and this extra edge. In the degree sum over A, branching at w spends one unit and the disjoint unmarked edge spends a second. Tightness permits only one.

The upper-block generalization derives the chain directly from the tree degree identity. In a hypothetical failure at deficit at most two, each parity tree with an internal root has exactly |D|−1 edges on D and no branching at a marked vertex. When the root memberships agree, a disagreement of minimum depth has an unmarked predecessor. Prescribing the parents in a shortest-path spanning tree forces all later disagreements onto the same chain. Applying the coloring argument in G produces a bipartite witness of order |V|−1; the published rank-one rooted theorem then contradicts failure. If the root itself is marked, extending its full star in the parity graph gives degree at most two in a failure. Biconnectivity gives the matching lower bound.

## Source and replay map

All theorem names below are in `Minimal180.DescentOne`.

| New module | Direct imports | Result |
|---|---|---|
| Spine180 | CutChain180 | Extract the published chain and its first and last steps |
| SpineTree180 | Spine180 | Preserve the chain, attachment and an extra edge, with a terminal leaf |
| Unmarked180 | SpineTree180 | Degree count and independence of the unmarked set in a failed cut |
| SpineBridge180 | Spine180 | The first alternating edge is a bridge |
| SpineLayers180 | SpineBridge180 | Root-component membership at every disagreement depth |
| SpineColor180 | SpineLayers180 | Bipartite coloring after deletion of the first tip |
| DeficitOneCut180 | SpineColor180, Unmarked180 | All-depth strict cut gain |
| MarkedFork180 | DeficitOneCut180 | Branching plus an edge outside the independent set |
| NoTightCut180 | MarkedFork180 | Nonexistence of the entire tight lower-deficit-one cut |
| TwoRigidity180 | Spine180 | Degree and edge-count equalities for a general deficit-two failure |
| BalancedSpine180 | TwoRigidity180 | Derive the chain for an arbitrary block with matching root memberships |
| BalancedBridge180 | BalancedSpine180, Unmarked180, SpineColor180 | General unmarked independence and alternating bridge |
| RankTwoRoot180 | BalancedBridge180 | Rooted inequality and exact degree restriction |
| RootPorts180 | RankTwoRoot180 | Transition gain and residual independent-set restrictions |
| BlockFamily180 | RankTwoRoot180 | Assembly and ordinary Graffiti.pc 180 on the stated family |

The cut proof and exclusion form one self-contained dependency group through `NoTightCut180`. The general block theorem reuses the spanning-tree and coloring arguments. The assembly corollary only needs `RankTwoRoot180` and its imports. The file `modules.txt` is a valid topological order for the entire bundle. No new C++ searches or finite-enumeration assumptions enter any result.

The 68 reused dependencies match published Git blobs in `vjdad4m/maths` at commit `de6b4b9f7cad3b9d04a53e9f642ecda4f93730ac`. Each upstream path and blob ID is listed in `published-blobs.txt`. Lean is 4.19.0, and Mathlib 4.19.0 is pinned at `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```sh
LEAN_BIN=/absolute/path/to/lean-4.19.0/bin MATHLIB_DIR=/absolute/path/to/mathlib4 bash graffiti-180-deficit-one-descent/verify.sh
```

The script checks the source manifests and recompiles the 68 imported modules in a fresh directory. It compiles every new module with warnings as errors and kernel-replays every new declaration against just that module’s imports. It checks every printed axiom report and rejects any new axiom, unsafe declaration or partial declaration. The clean replay compiled 68 pinned imports and 15 new modules, replayed all 165 new declarations, and checked 25 axiom reports. Each report lists exactly `propext`, `Classical.choice` and `Quot.sound`. 

The unrestricted conjecture, tight cuts with larger lower deficit, and the remaining singly marked degree-two rooted cases are unresolved in this work.
