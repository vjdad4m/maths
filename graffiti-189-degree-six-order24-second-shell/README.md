# Graffiti.pc #189, degree six: second shells at orders 24 and 25

Assume a finite connected simple graph with at most seven vertices at
even distance from each vertex, at most one degree below six, and
connectivity preserved by deleting fewer than three vertices.
If the graph has at least 24 vertices, every degree-at-most-six vertex
has at least four vertices at distance two. This joins the order-25 result
with a complete analytic order-24 exclusion of second-layer size three.
The checked theorem is
`Graffiti189LongestPath.four_le_second_shell_of_order_ge_twenty_four_at_degree_six`.
It is a structural reduction and not a spanning-path theorem.

At order 24 the established radius bound and three-vertex second layer
leave first-, third-, and fourth-layer sizes (5,12,3), (6,12,2),
or (6,11,3). A full selector's second-layer representative pays
distance-two slots for the root, all fourth-layer vertices, missing
spare first-layer neighbors, other adjacent selectors, and foreign
third-layer endpoints of cross edges.

* When the third layer has size 12, its groups are disjoint four-sets.
  At (5,12,3) there are no foreign cross edges; at (6,12,2) each group
  has at most one foreign endpoint. A carefully chosen high vertex
  then shares a fourth-layer neighbor with at least seven nonadjacent
  high vertices from other groups.
* At (6,11,3) all three full groups would have one shared member.
  There are no foreign cross edges, so that member has degree at most
  five. A high exclusive member of either overlapping group sees
  all seven vertices outside its own group at distance two.
* Alternately the groups have sizes 3,4,4 and are disjoint. The
  deficient selector can spare only one even slot, so it must be
  adjacent to at least one full selector. This leaves at most one
  cross-edge endpoint in its third-layer group. A high noncrossing
  member of that group meets all three fourth-layer vertices;
  every high foreign vertex meets at least one. This again costs
  at least seven distance-two vertices.

## Replay

Use Lean/Mathlib v4.19.0 with the preceding packages and their
transitive objects in LEAN_PATH:
[order-24 radius](../graffiti-189-degree-six-order24-radius/),
[order-25 second-shell](../graffiti-189-degree-six-order25-second-shell/),
and [universal order-25 bound](../graffiti-189-degree-six-order25-universal/).
Compile the seven modules in StrictReplay.log order with
`-j1 -s32768 -DElab.async=false -DwarningAsError=true`.
Only standard Lean axioms, no SAT or graph enumeration.
