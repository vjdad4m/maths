# Graffiti.pc 180 — eligible leaves at a cut

The exact cut criterion is `Minimal180.CutGain.cut_gain_iff_wings`. At lower bipartization deficit one, `Minimal180.CutGain.TightCut.tight_exit` transfers any putative failed cut-triangle transition to a deeper, equally tight transition of a different type on the same upper graph. Consequently every maximum-depth horizontal cut-triangle transition at this deficit gains an eligible leaf. These results leave the general conjecture open.

## Hypotheses and notation

Write G=J+xy, where the finite simple lower graph J is connected, xy is absent and x–w–y is a lower path. A proper split has sides S and T, both smaller than the whole graph, meeting only at w. All lower edges lie in one side. The tip x is exclusive to S and y is exclusive to T. Let ℓ(H,U) be the largest number of vertices in U that are leaves of one spanning tree of H. The bipartite order b(H) is the maximum order of an induced bipartite subgraph.

The structure `TightCut` additionally requires order at least four, an upper graph without a cut vertex, upper rooted sparsity, an upper horizontal chord, an upper independent mark A, a parity choice defining P, rank drop b(J)=b(G)+1, and the equality ℓ(J,U)+b(J)=1+|A|+|P|. Here U consists of A∪P, with the root removed unless it belongs to both marks. The root lies on the named near side S. A split can be reoriented before invoking this structure. Rooted sparsity means deleting any edge for which neither endpoint is the other’s unique shortest-path predecessor increases the bipartite order by one.

## Strict results

1. **An exact two-wing test.** Suppose |V|≥4 and the upper graph with w deleted is preconnected. For any eligible set U, adding xy increases ℓ exactly when w∈U and both wing optima for U minus w survive the following restriction. On the x wing delete all edges at w except wx. On the y wing keep only wy at w. Each equality is a local calculation on a smaller graph. The test uses arbitrary spanning trees and assumes neither tightness nor rooted sparsity. Without a cut, eligibility of w and preservation of the old global score after keeping only wx and wy are still necessary.
2. **The doubly marked seam.** At any bipartization deficit in a tight horizontal cut with w∈A∩P, gain follows from the ordinary rooted bounds on the two smaller sides. The exact inputs in `horizontal_double_gain` are the two bounds quantified over their local parity choices. At lower deficit one, gain is equivalent to w∈A∪P under the full `TightCut` hypotheses, without either smaller-side bound. Moreover w∈A∪P forces A=P.
3. **Mark rigidity in a failed deficit-one transition.** Put D=(A∪P)∖(A∩P). The seam is unmarked, both tips belong to P, and exactly one belongs to A. The doubly marked tip's wing has no disagreement. Any pendant tip must be this doubly marked tip. The previous odd-block result supplies a pendant wing at deficit one. The root lies outside D, |P|=|A|+1, and there is a first disagreement t at the other tip. There is at most one disagreement at each depth. Each disagreement after t has a unique predecessor in all of J, and that predecessor lies in D. Thus the disagreements form a single shortest-path chain beginning at t.
4. **A second exact tight transition.** There are lower neighbors q,z strictly deeper than the original tips, with q∈P∖A and z∈A∩P, at the same root distance. The edge qz has no common predecessor in G. Let K=G−qz. It is connected and nonbipartite, keeps P and A, satisfies b(K)=b(G)+1 and ℓ(K,U)+b(K)=1+|A|+|P|, and has ℓ(K,U)=ℓ(G,U). Either K has no cut vertex or q and z have no common lower neighbor. This is an actual second tight zero-gain transition under the assumed original failure. The proof uses the published rank-one rooted inequality on K. No minimal-counterexample assumption enters.
5. **A positive gain class.** If every deeper horizontal lower edge has endpoints with a common upper predecessor, strict eligible-leaf gain follows in the original cut triangle at deficit one. In particular gain holds whenever the original chord is at maximum horizontal-edge depth. Neither conclusion assumes local bounds on smaller graphs.
6. **Connection with #177.** For any finite connected graph H of order at least two, independent Q⊆U gives 2|Q|+1≤ℓ(H,U)+b(H). Decorate the complement of U by pendants, apply the published #177 and cancel the pendant counts. This forces 2|Q|<|A|+|P| in a failed tight upper graph and helps determine the length and endpoints of the disagreement chain.

The argument for the deeper edge applies the published confined-parity theorem to P with the first tip erased. At the forced cardinality this would already give upper gain if the remainder were independent. A surviving edge in that remainder has one disagreement endpoint. Its unique predecessor belongs to A, as does the opposite endpoint of the horizontal edge. Independence prevents it from being their common predecessor. A horizontal cut-triangle edge always has such a predecessor, giving the structural alternative.

At every deficit, a real `TightCut` with an unmarked seam would lift to an ordinary connected counterexample to #180 of order at most 4|V|−1 by `unmarked_counterexample`. No such graph was obtained here. At deficit one the smaller cut-triangle case can be discharged by resolving the biconnected-lower or no-common-neighbor alternatives in the same upper graph. Higher deficits still permit other unresolved seam patterns.

## Source map

| New module | Direct imports | Main checks |
|---|---|---|
| SpokePrune180 | SeamBudget180, WingCertificate180 | Necessary pruning of the old spokes |
| CutGain180 | SpokePrune180 | Exact cut and independent wing criteria |
| MarkedPort180 | CutGain180, TightWing180 | Preparing a marked port, double-mark gain |
| CutGeometry180 | MarkedPort180 | Root geometry and precise smaller-side hypotheses |
| BranchLayer180 | CutGeometry180 | Simultaneous branching with both prescribed spokes |
| DefectOneGain180 | BranchLayer180 | Full transition data, deficit-one decision, bounded lift |
| CutSupport180 | DefectOneGain180 | Single-wing support and pendant mark |
| Weighted177Gain180 | DefectOneGain180 | Weighted #177 and independent-set obstruction |
| CutEntry180 | CutSupport180, Weighted177Gain180 | Single shortest-path entry and cardinal bias |
| CutChain180 | CutEntry180 | Exact mark difference and unique-predecessor chain |
| CutEscape180 | CutChain180 | Deeper rank drop without a common predecessor |
| CutExit180 | CutEscape180 | Exact second tight zero-gain transition |
| CutOutermost180 | CutExit180 | Unconditional gain for outermost cut triangles at deficit one |

The 58 files in `foundation/` matched the public repository by Git blob at commit `c74fa0ec0bbaf4aeb5e7231f5bd39d2e414f1d6d`. The individual paths and hashes are in `published-blobs.txt`. There are 49 from the chord-criteria package, seven from odd-blocks, one from core-exchanges and one from private-neighbor-repairs. The transitive imports include the published #169, #177 and degree-#179 sources.

## Replay

Use Lean 4.19.0 and the compiled Mathlib 4.19.0 checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Run from this directory in the repository checkout.

```sh
LEAN_BIN=/absolute/path/to/lean-4.19.0/bin MATHLIB_DIR=/absolute/path/to/mathlib4 bash verify.sh
```

The verifier checks both SHA-256 manifests, loads the exact public foundation sources into a fresh directory, compiles each of the thirteen result modules with warnings as errors, and replays every new constant into an environment containing only that module’s imports. It rejects new axioms, partial declarations and unsafe declarations. The final audit checks that each printed axiom report lists exactly `propext`, `Classical.choice` and `Quot.sound`. The clean replay accepted 149 new declarations. All 31 printed axiom reports used exactly those three axioms. 

## Enumerated evidence

This separate C++ experiment exhausts unlabelled biconnected graphs of orders 3–9, and those of order 10 with 10–15 edges. A further fixed set of 141 records of orders 8–16 comes from earlier searches. For each nonbipartite graph it intersects all maximum bipartite sets and tests ordered adjacent ports w,x in that intersection with the tip one level beyond w. It enumerates independent marks, roots, both parity choices and both applicable wing roles. Complementary connected dominating sets give the exact eligible-leaf score on each tested wing of order at least three.

For a wing B use k=1+|A_B|+|P_B|−b(B)−ℓ(B,U_B), where U_B erases w and applies the root rule on the near side. The comparison cap is the indicator that w belongs to the union of the marks on the near side and to their intersection on the far side. The sum of the caps is the seam correction in the published cut-budget identity.

| Collection | Input graphs | Marked port tests | At cap | Over cap |
|---|---:|---:|---:|---:|
| All biconnected, orders 3–8 | 7,661 | 7,953,064 | 10,615 | 0 |
| All biconnected, order 9 | 194,066 | 350,891,758 | 77,912 | 0 |
| Biconnected, order 10 and 10–15 edges | 30,433 | 251,635,594 | 47,293 | 0 |
| Fixed earlier records | 141 | 15,720,430 | 28,780 | 0 |

Every saturation in these tests had w outside both marks and the tip in A. The outward depth then puts the tip in P as well. Pairing two tested wings at saturation would put both endpoints of the added chord in the upper independent mark. This rules out tight pairings of two nontrivial wings in the enumerated families in the finite computation. The tables count rooted marked configurations, with multiplicity across roles and labels of ports within a graph. They give no universal local bound.

The enumeration reruns with a C++20 compiler and nauty 2.9.3.

```sh
GENG=/absolute/path/to/geng bash search.sh
```

The script regenerates each row and compares its output byte for byte with the saved counts.
