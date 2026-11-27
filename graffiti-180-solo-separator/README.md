# Graffiti.pc 180, the single-protected degree-four case

This package proves structural reductions and an explicit repair for the stronger protected witness used by the prime-quotient proof of Graffiti.pc 180. The unrestricted conjecture and the general single-protected case remain open in this work. The two-protected case is separate.

## Marking and budget

Let G be a finite simple connected graph with at least two vertices. Fix a root r, a distance parity P and an independent set A. The protected vertices are K = A ∩ (P ∪ {r}). The exact deletion allowance B equals the maximum eligible-leaf count plus |V| − (1 + |A| + |P|). A protected witness is equivalent to deletion of at most B vertices outside K to obtain an induced bipartite graph. In the residual branch, {a,b} is a transversal, a is the sole protected tip and a ≠ r. The frozen rigidity theorem forces degree(a) = 4 and B = 2 in any failed marking. It also forces balance on every component of R = G − {a,b}.

## Graph-wide reductions

* `protected_join` assembles arbitrary protected witnesses across a cut vertex, with the root and parity transported separately to the two wings. `allowance_join` proves that their exact allowances sum to at most the global allowance.
* `solo_cut_protected` settles the marking when a is a cut vertex. In either wing the degree of the seam a drops. A wing containing b cannot have a failed single-protected marking by degree-four rigidity. A wing without b has transversal number at most one. Consequently `solo_components_touch` proves that every nonempty union of components of R touches b in a failed marking.
* For a graph with transversal number at most two, `saturated_wing_bip` proves that every cut wing away from a doubly marked vertex a with degree(a) = B + 2 is bipartite. Its original degree is retained on its own wing, consuming the full allowance there.
* `inactive_free` and `active_core_iff` let one discard all components of R that avoid the neighborhood of a. Those vertices can all be restored at no deletion cost, both when b survives and when b is deleted. This also applies when just one component touches a.

## Two active components

If a component touches a, balance supplies neighbors on both sides of its bipartition. A path between them makes an odd cycle through a. `mixed_of_balance` formalizes this implication. Two such disjoint components C and D force every budget-two witness retaining a to delete exactly one vertex from each. It must retain b.

`active_contacts_iff` fixes any proper coloring of R. For each sign t, check each active component separately. Choose one unprotected deletion inside the component and examine the connected components that survive the deletion.

1. In each surviving component, all contacts of a have a common old color. All contacts of b also have a common old color.
2. If a surviving component sees both tips, equality of the two old contact colors must have truth value t.

The marking admits a protected witness if and only if a common sign passes both active regions. The union of all inactive regions places no condition on the sign. The theorem assumes the explicit two-region partition, an odd-cycle obstruction through a on each side, degree four and the exact allowance two. `both_signs_iff` identifies precisely when either sign is available after a specified deletion. In addition to local color coherence, no surviving path may join a contact of a to a contact of b.

`solo_flexible_repair` gives a sufficient condition formulated directly on the original coloring and the single-protected marking. In the first active region the two center-neighbors have opposite colors and all contacts of b have the same color. In the other region a single unprotected deletion makes the remaining contacts of each tip monochromatic. The first region can match either sign by choosing the appropriate center-neighbor to delete. The proof also covers a priori unspecified allowances using the frozen rigidity result for a hypothetically failed marking.

## Four-neighbor alternative

`protected_ports_iff` splits a repair into deletions outside the closed neighborhood of a and retained neighbors of a. All joint component-flip constraints on the retained neighbors are equivalent to the constraints for their one- and two-element subsets. If the four neighbors admit no independent triple, `four_ports_iff` shows that both deletions must be neighbors. It suffices to check the six pairs for a single outside coloring. Two independent edges that cover the neighborhood imply the independence bound.

## Strict finite regressions

* On the frozen eight-vertex recoloring graph, the retained neighbor pairs of 0 are exactly {3,6} and {3,4}. The witness must keep the unprotected tip 5 and change the relative color of 1 and 2. See `Eight.exact_port_pairs` and `Eight.four_port_regression`.
* A nine-vertex prime graph at root 6 has two balanced active components. After one deletion each, one requires equal tip colors and the other requires opposite tip colors. Every repair keeping vertex 0 costs at least three, and the explicit deletion {1,2,4} costs three and retains all pins. Its exact allowance is three. Both its protected marking and ordinary 180 are proved. See `Nine.opposite_signatures`, `Nine.pinned_cost`, `Nine.budget` and `Nine.slack_regression`. This gives a counterexample to imposing a common sign from component balance alone.
* A different nine-vertex prime graph at root 1 has degree-four center 0 and allowance two. Its two old components both have contacts of the other tip in opposite colors in every initial coloring. The first component allows only opposite terminal colors. In the second, deleting 8 leaves both signs possible. The common opposite sign produces the protected witness. See `Tight.no_fixed_monochrome`, `Tight.masks` and `Tight.tight_regression`.

The full general result would still have to guarantee a passing one-component repair or guarantee intersection of the two local sign sets at allowance two. The allowance-three incompatible example does not resolve the latter question.


## Replay

Use Lean 4.19.0 and pinned Mathlib v4.19.0. Build the [nonadjacent-repair predecessor](../graffiti-180-nonadjacent/) and its prerequisite Lean modules first. Put their objects on the Lean search path, then build the sources here by the first column of `modules.txt` with synchronous elaboration and warnings as errors. Put newly built objects on that same search path. The exact source digests and strict replay transcript are included. The regressions are not counterexamples to the full conjecture.
