# Graffiti.pc #189: degree-six order-16 adjacent singleton, six visible and no balanced dark vertex

Let a finite connected simple graph satisfy singleton-deletion connectivity,
the degree-six threshold (all but at most one vertex have degree at least
six), and the cap of seven even-distance vertices from each vertex (including
itself). If an adjacent two-vertex separator leaves precisely a singleton
and a thirteen-vertex shore, the larger shore has six visible vertices,
and no dark vertex is at distance two from both endpoints of the cut,
then the original graph has a spanning path.

Lean derives the port and dark geometry, including a seven-vertex dark
block of internal minimum degree at least four and active roots on both
sides. The finite routing certificates cover exclusive counts (2,2)
and (1,2). A labeled spanning path uses terminal Ore for the dark
block, followed by a checked visible port route. The explicit equivalence
transports the path to the original arbitrary vertex type. A symmetric case
dispatcher handles (2,1), and the previously checked unique-exclusive
theorem handles (1,1).

Main declaration:
Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_of_adjacent_singleton_thirteen_six_zero_balance.

Replay with Lean/Mathlib 4.19, the prior published degree-five cut/Ore stack,
the degree-six singleton/nonadjacent and adjacent unique packages, and
the five-visible at-most-one-balance package on LEAN_PATH. The proof uses
only standard axioms. This closes the zero-balance branch, not the full
adjacent case or the full conjecture.
