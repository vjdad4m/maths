# Graffiti.pc #189: small minimum cuts cannot split three nontrivial shores

For a finite connected simple graph, use the original #189 bounds: each
vertex has at most d other vertices at even distance, and at most one
vertex has degree below d. Let S have cardinality k≥2 and assume deletion
of any set with fewer than k vertices keeps the graph connected. If
outside S the vertices partition into three mutually nonadjacent sets
each of cardinality ≥2, then **d + 6 ≤ 6k**.

Thus when d>6k−6 a minimum cut cannot have three nontrivial shores. If the
graph has at least three components outside a minimum cut, grouping
components gives this same obstruction except when there are exactly
three and one of them is the unique low-degree singleton. The checked
theorem takes the three-shore partition directly. It does not prove
traceability or resolve unrestricted #189.

The proof uses one cut vertex s with a high neighbor in each shore.
Every cut vertex touches every shore by minimality. If one shore
contains the unique low vertex, some cut vertex touches a high vertex
there, since otherwise that low vertex alone would disconnect the shore.
The three high witnesses charge their own internal neighbors not
adjacent to s against the distance-two budget at s. Conversely, each
witness spends its own distance-two budget on all s-neighbors in the
other two shores. The two counts give the inequality.

Main theorem:
`Graffiti189LongestPath.ThreeShoreCutBound.degree_le_of_minimum_cut_with_three_nontrivial_shores`.
Replay with Lean 4.19 and SmallSeparator189 on LEAN_PATH.
