# Graffiti.pc #189: two more order-fourteen singleton-shore profiles

In the degree-five adjacent-cut branch, suppose deleting the adjacent
terminals leaves a singleton shore and an eleven-vertex shore. If the
large shore has one even-distance vertex equidistant from the terminals,
one strict-odd vertex on each side, and the strict-even classes each have
at least two vertices and together at least five, then the graph has a
spanning path (assuming at most three equal-odd vertices). This closes
two of the seven profiles in the previous frontier and leaves five.

The dark part of the eleven-vertex shore admits a terminal-preserving
Ore completion. One possibly exceptional dark vertex can be inserted
into the closed clique or moved to the end of the common-port path.
The other pieces concatenate through the singleton and both terminals.

Public declarations:
- Graffiti189LongestPath.CrossSaturation.FiveAdjacent.traceable_of_adjacent_singleton_eleven_equal_one_unique
- Graffiti189LongestPath.CrossSaturation.FiveAdjacent.narrowed_frontier_of_adjacent_singleton_eleven_counterexample

Use Lean 4.19.0, Mathlib 4.19.0 and the checked predecessor objects on
LEAN_PATH, especially the order-fourteen singleton frontier, mixed
adjacent routing, and full-distance-two terminal Ore packages. Run
replay.sh, which uses the order in order.txt. LEAN-CHECK.txt contains
standard-axiom reports. This is not the full conjecture.
