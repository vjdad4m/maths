# Graffiti.pc #189: complete nonadjacent degree-six cuts at order sixteen

Let a finite connected simple graph remain connected after any single
vertex deletion, have at most one vertex of degree below six, and have
at most seven even-distance vertices at any vertex (including itself).
If its order is sixteen and some nonadjacent pair is a genuine
two-vertex separator, the graph has a spanning path. There are no
assumptions on the two shore sizes. Distance-three cuts were covered
through order 18, nonsingleton cuts were covered through order 16,
and the earlier order-16 singleton package covered at most two
balanced dark vertices. This package closes the final three-balanced
singleton profile and joins these results.

In the three-balanced profile each terminal's distance-two budget
is fully occupied by five nearby dark vertices and the other
terminal. The exclusive ports therefore touch neither each other
nor the common ports; high degree forces them to touch all three
balances. A common port touching two balances would see all four
strict vertices at distance two, as well as the singleton and both
exclusive ports. Hence each common port touches exactly one balance,
and degree forces all four common ports to form a clique.

If the balance chosen to meet the common clique has strict neighbors,
the dark routing lemma starts at a different balance, crosses the four
strict vertices with the third balance inserted, and ends at the
chosen balance. The missing strict edges form a matching, which permits
the needed endpoint selection. If the chosen balance has no strict
neighbor, the other two balances meet all four strict vertices, and
terminal Ore routes the dark subgraph after removing the chosen one.
Real paths and support-disjoint joins construct the spanning path.

Main checked declarations:
- Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_of_nonadjacent_singleton_thirteen
- Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_at_six_nonadjacent_order_sixteen

Run replay.sh with Lean and Mathlib 4.19.0, with the earlier actual and
normalized singleton cases, nonsingleton order-16, and cut / Ore packages
on LEAN_PATH. Every axiom audit contains only standard axioms.
Adjacent singleton cuts and higher orders are not settled here.
