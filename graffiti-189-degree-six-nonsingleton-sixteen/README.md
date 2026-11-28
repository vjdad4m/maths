# Graffiti.pc #189: nonsingleton degree-six cuts through order 16

Assume a finite connected simple graph staying connected after a single
vertex deletion, with at most one vertex below degree six and at most
seven even-distance vertices from each vertex, including itself. If an
actual two-cut has no singleton component and the graph order is at most
16, it has a spanning path. This does not require the terminals to be
adjacent or at any specified distance.

The two shores both have order at least five, so each has at most nine.
High vertices of either shore have local degree at least four. When a
high vertex has local degree four, it is common to both terminal
neighborhoods, so all visible vertices in the other shore use its
distance-two budget. Shores of order five or six are almost entirely
visible. An all-high 8-shore, or the high vertices of a 9-shore, could
not have local degree four: at least three local high nonneighbors
are at distance two (their local neighbor sets must intersect), and at
least four foreign visible vertices then violate the budget.

The all-high shore admits a spanning path between ports of opposite
colors by ordinary terminal Ore. The other shore admits a spanning
path rooted at a port by the two-root Ore theorem. Splice the free
shore to the middle via its chosen terminal and append the other
terminal. The sole remaining order-16 actual-cut possibility is a
singleton and a shore of order thirteen.

Main declaration:
`Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_at_six_nonsingleton_shores_order_sixteen`.

Use Lean and Mathlib 4.19.0 and the checked predecessor modules on
LEAN_PATH, including the degree-six exact-two component result and
the prior terminal and two-root Ore tools. Run replay.sh to verify
hashes and compile. Only standard axioms are used.
