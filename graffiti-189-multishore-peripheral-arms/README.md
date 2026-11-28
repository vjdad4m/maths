# Graffiti.pc #189: cut-shore counts and peripheral-arm obstruction

Work in a finite connected simple graph where every vertex has at most d
distance-two vertices (implied by the original even-distance budget), and
at most one vertex has degree below d. Assume deletion of fewer than k
vertices preserves connectivity.

A partition outside a k-vertex separator into q≥2 nontrivial pairwise
nonadjacent shores, with k≥2, satisfies
[
((q-1)^2-q)d+q(q-1)le q(q-1)k .
]
For example q=3 recovers d+6≤6k, and q=5 gives 11d+20≤20k.
If 2k≤d the bound forces q≤4.

The same bound holds without any partition assumption for q≥2 disjoint
nontrivial peripheral arms after deleting k−1 vertices, provided k≥3.
Each arm must have just one possible attachment to the remaining region
outside the arm; the different attachments need not agree. The unrestricted
center may be nonempty. This excludes three such peripheral arms when
d>6k−6. It is a structural result, not a traceability theorem.

The common-gate lemma does not assume any cut or coverage: it suffices
that one vertex outside all shores reaches high witnesses in all of them
and that each witness has at most k neighbors outside its own shore.
Their neighbors in the other shores charge their distance-two budgets;
their internal neighbors missed by the shared gate charge its budget.

Main theorems in `Graffiti189LongestPath.MultiShoreCutBound`:
`degree_le_of_minimum_cut_with_many_nontrivial_shores`,
`at_most_four_shores_below_half`, and `degree_le_of_peripheral_arms`.
Replay the two files in this order with Lean 4.19, with the built
`SmallSeparator189` dependency and Mathlib on LEAN_PATH. We used
`-j1 -DElab.async=false -DwarningAsError=true`; only standard axioms.
