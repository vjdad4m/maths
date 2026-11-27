# Graffiti.pc #384b for 31 triangle counts and 30 nonleaves

For every finite connected simple graph G with exactly 31 distinct vertex triangle-incidence counts and exactly 30 vertices of degree at least two, there is a 2-dominating set of size at most |V(G)| − 16. Zero belongs to the set of counts whenever a vertex realizes it. A set 2-dominates when every vertex outside it has at least two neighbors in it. The assertion places no additional restriction on the order of G. [Lean theorem `exact_thirty_nonleaves`](DisjointFinish31.lean)

This proves the catalogue inequality on the specified profile. The common-neighbor and disjoint-neighborhood cases have separate source packages. The common-neighbor source is included here as a dependency. Cases with other combinations of diversity and nonleaf count are outside the theorem. [Common-neighbor proof](CommonSaving31.lean) · [Shared result index](https://github.com/vjdad4m/maths/blob/main/README.md)

## Proof

Assume the bound fails. The predecessor reduces the problem to the induced graph H on the 30 nonleaves. Its triangle counts are positive and pairwise distinct, and γ₂(H) = 15. It has nonadjacent cubic vertices u and s with triangle counts two and three. Their neighborhoods U and L are disjoint after applying the common-neighbor theorem. Every five-clique meets B = U ∪ L in at least three vertices. [Previous reduction and new conclusion](DisjointFinish31.lean)

The six vertices of B and the two cubics leave an exterior W of size 22. Choose x in U and y in L. Include the four vertices of B outside {x,y} and eight vertices sampled from W. Both cubics have two included neighbors. Since L induces a triangle, y also has two. Since U induces a three-vertex path, x has at least one. Complete the set by including each unsampled exterior vertex needing a second neighbor and x if needed. At most two repairs suffice to give a set of size 14. [Construction and coverage](DisjointRepair31.lean)

Count repairs over the nine choices of (x,y) and all eight-subsets of W. A vertex w of W with at most two neighbors in B cannot have a four-clique in its neighborhood, since this would give a five-clique violating the intersection bound. For x in U, a repair is possible only if it sees one other vertex of U and at most one vertex of L. If x sees one vertex of L, only the rotations omitting that particular y can require repair. [Triangle-count bounds](DisjointGeometry31.lean) · [Counting the nine choices](DisjointRotation31.lean)

The budget ranks all 28 vertices in W ∪ B. Their positive, distinct triangle counts omit two and three. Charge 11,111 units at the exterior end of each edge joining W and B, and credit the same amount to its endpoint in B. The two sums agree by double counting. The rank table gives a total of 9,217,200 units, including an allowance of 100,000 for each of the six anchors. Thus there are at most 8,617,200 repairs over all trials. Three repairs in every trial would require 27 × C(22,8) = 8,633,790, a shortfall of 16,590. At least one trial yields γ₂(H) ≤ 14, contrary to γ₂(H) = 15. Lean checks both the finite inequalities and their coverage of every graph satisfying the premises. [Finite budget](DisjointBudget31.lean) · [Averaging proof](DisjointSaving31.lean)

## Replay

Use pinned Mathlib v4.19.0 and Lean 4.19.0. Add the compiled [thirty-nonleaf reduction](../graffiti-384b-thirty-nonleaves/) and its dependency objects to the Lean search path. Compile every source in `modules.txt` order, with `-DElab.async=false -DwarningAsError=true`, keeping newly built objects on the search path. The shared-neighbor log is `StrictCommon.log`; the final disjoint-neighborhood and graph-level integration log is `StrictDisjoint.log`. The full conjecture remains unresolved.
