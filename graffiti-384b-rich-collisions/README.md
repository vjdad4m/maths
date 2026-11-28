# Graffiti.pc #384b on rich components with few triangle counts

For a finite simple graph G let s(v) count the triangles incident to v and let t count all distinct values of s, including zero when it occurs. A 2-dominating set gives each vertex outside it at least two neighbors in the set. The catalogue bound for connected graphs on n > 2 vertices is γ₂(G) ≤ n − ⌈t/2⌉.

Let H be the subgraph induced by the vertices with s(v) ≥ 2. Let i(v) count the triangles at v in H and put d(v) = s(v) − i(v). **The catalogue inequality holds at every order if H has at most three distinct internal triangle counts.** This includes nonconstant connected rich cores. The theorem uses the actual induced simple graph and its usual triangle invariant. [RichBlockFinish.lean](RichBlockFinish.lean)

A separate local conclusion holds for any nontrivial component C of H, even when other components have arbitrarily many internal score levels. Each of the following conditions suffices individually for the catalogue inequality.

* C has at most five vertices.
* C has at most two distinct internal scores, at any separation.
* The largest and smallest internal scores on C differ by at most two.

The Lean statements also allow any nontrivial union of rich components satisfying the indicated condition. The singleton case is excluded in these local results. [RichBlockFinish.lean](RichBlockFinish.lean)

## Duplicates and ear incidences

In the graph J of triangle edges of G, take any maximal independent set F of score-one vertices. Each triangle lost at a rich v contains exactly one member of F. Consequently d(v) is exactly the number of neighbors of v in F in the graph J. [EarRepresentatives.lean](EarRepresentatives.lean)

In a strict failure at most one rich vertex has d(v) = 2 and every other rich vertex has d(v) ≤ 1. If the double loss occurs, every ear of F has two rich neighbors and the total loss on the rich set equals 2|F|. The proof double-counts ear–rich incidences and uses the checked anchor floor 2|F|−1. [CollisionBudget.lean](CollisionBudget.lean)

For any set P of internal scores, the number of rich vertices lying over P is bounded by the number of values at least two in P ∪ (P+1), plus the number of double-loss vertices lying over P. Here P+1 is the elementwise shift. Thus all choices of levels share a single exceptional vertex. If r is the number of values of i on H and score one occurs, a failure requires t ≤ 2r+3. Odd r improves this to t ≤ 2r+1. At the extremal rich cardinality 2r+1 the zero-loss and one-loss layers each have r vertices. The total loss r+2 must then be even. [CollisionPalette.lean](CollisionPalette.lean)

## Ear exchange and the five-vertex proof

If an ear has both its triangle neighbors universal in a closed rich block C of size at least four, the catalogue bound holds. One can omit the ear and the other vertices of C while retaining both neighbors. The predecessor's donor obstruction supplies the remaining omissions. An exterior rich vertex has no triangle edge into C and therefore cannot obstruct the exchange. In any failure, for every subset U of vertices universal in C, the total loss on U plus the number of double-loss vertices in all of H is at most the loss on C minus U plus one. This compares the two endpoints of each ear against the shared incidence budget. [UniversalEar.lean](UniversalEar.lean)

An arbitrary closed rich block labelled by Fin n must therefore carry a vector of losses in {0,1,2}. Its reconstructed scores are distinct and at least two, at most one loss is two, and the universal vertices satisfy the preceding inequality. The Lean theorem transports internal counts to the labelled induced graph and transfers all four conditions. [RichBlockModel.lean](RichBlockModel.lean)

On a five-vertex closed block, some vertex must have internal score at least four. Otherwise its five distinct original scores would all be in {2,3,4,5}. Such a vertex is universal, so six independent Boolean variables encode every possible graph on its other four vertices. Lean checks a root-fixing relabelling for all 64 patterns. Seven of the eleven resulting graph types have root score below four. For each of the other four, Lean computes the actual five scores and the universal vertices, then rejects all 3⁵ loss vectors by kernel reduction. The case with two to four vertices follows from the local count bound and the forced four-clique at internal score three. External search supplies no coverage in this proof. [FiveEarCodes.lean](FiveEarCodes.lean) · [FiveEarNormal.lean](FiveEarNormal.lean) · [FiveEarTable.lean](FiveEarTable.lean) · [CollisionBlock.lean](CollisionBlock.lean)

## Exact examples and open scope

One eleven-vertex connected graph has a single leaf, with every other edge in a triangle. Its seven rich vertices have distinct original scores 7,3,2,4,5,10,8 and losses 2,0,1,1,0,2,0. Its two-domination number and its catalogue bound both equal six. The restriction to one double loss thus depends on strict failure even under the earlier pointwise loss bound. Lean verifies both the explicit dominating set and the exclusion of every dominating set of size at most five. [CollisionExample.lean](CollisionExample.lean)

The four local feasibility conditions alone permit a six-vertex block. The graph with internal scores 3,3,1,5,6,6 and universal vertices 4 and 5 passes with losses 0,1,1,0,0,1. A ten-vertex graph realizes those losses on this induced rich graph and has a five-vertex 2-dominating set. This limits the five-vertex checker's reach. Targeted computation suggested the two fixtures. All reported properties are certified on the supplied graphs. [SixLossExample.lean](SixLossExample.lean)

The general single-leaf ear case with at least four internal types and larger nontrivial components of wider score range remains subject to the preceding restrictions. This package gives no general resolution or catalogue counterexample.

## Reuse and strict replay

The embedded predecessor is the exact 99-module source archive inside the public rich-core ear-kernel package. The new proofs use its rich-score injectivity, incidence floor, loss bound, induced-graph invariant, and donor obstruction. The public private-triangle extension was compared at the source level. Its simultaneous extension requires a frame reserving a disjoint free triangle for every deficient pin along with the no-thin-pair condition. A maximal independent representative family supplies neither reservation condition in general. The local exchange here directly uses the two universal neighbors and allows additional ears or adjacent score-one vertices. [Predecessor](https://github.com/vjdad4m/maths/tree/main/graffiti-384b-rich-core-ear-kernel) · [Private-triangle theorem](https://github.com/vjdad4m/maths/blob/main/graffiti-384b-private-triangle-extension/PrivateTriangleExtension.lean)

Set CROSSFOUR_LEAN_BIN to the bin directory of Lean 4.19.0 and CROSSFOUR_MATHLIB to built Mathlib v4.19.0 at c44e0c8ee63ca166450922a373c7409c5d26b00b. Extract the source archive and run

~~~sh
python3 -B replay_collisions.py
~~~

The default entry rebuilds all 111 project modules. To reuse a complete predecessor run, pass --predecessor-log with its absolute log path. In either mode the driver checks all 99 predecessor object hashes and each of the twelve new object hashes. Strict elaboration treats warnings as errors. The axiom audit permits propext, Classical.choice and Quot.sound. The flat manifest gives the source and hash of every project module. [Manifest](ALL-SOURCES.tsv) · [Replay entry](replay_collisions.py) · [Predecessor identity](PREDECESSOR.txt)

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
