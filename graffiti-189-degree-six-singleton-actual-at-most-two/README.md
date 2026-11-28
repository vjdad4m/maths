# Graffiti.pc #189: exact order-16 nonadjacent singleton through two balances

Assume a finite connected graph remaining connected after a single vertex
deletion, with at least degree six at all but at most one vertex and at
most seven even-distance vertices from every vertex, including itself.
If a cut pair at distance two separates a singleton and a thirteen-vertex
shore, and at most two vertices of the large shore are nonvisible and
equidistant from the terminals, then there is a spanning path.

The degree conditions force each terminal to have at least five large-shore
ports. The singleton limits the visible count to six, and the case of five
common ports would violate the even budgets, so there are exactly six.
All seven remaining vertices have nearest-terminal distance exactly two:
odd-depth vertices would overflow the singleton budget, and larger even
depth requires a predecessor at odd depth. Neither port set can contain
the other because that would put all seven dark vertices at distance two
from one terminal. Hence there is one exclusive port per color and four
common ports. Each strict dark vertex adjoins only its exclusive port
among the visible vertices and consequently has at least five dark
neighbors. Both strict classes have at least two vertices, because the
terminals have only five unspent distance-two slots after counting each
other. The graph is explicitly relabeled to the exact normalized board
and the already checked normalized route transports back by isomorphism.

Main theorem:
Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_of_nonadjacent_singleton_thirteen_at_most_two_balanced.

Run replay.sh with Lean and Mathlib 4.19.0, plus the normalized singleton
order-16 package, cut and Ore predecessors on LEAN_PATH. Audit uses only
standard axioms. Three balanced vertices and adjacent cut pairs are not
covered by this result.
