# Graffiti.pc #189: four centers at any two-separator

For a finite connected simple graph that stays connected on deleting any
one vertex, suppose deleting distinct a,b disconnects the graph. If
every vertex has at most d+1 vertices at even distance including itself,
then its order is at most 4d+2. The two terminals need not be adjacent;
the number of components after deletion is unrestricted. There is no
degree lower bound. When d=6, the order is at most 26.

To see the improvement over a six-center argument, split the graph into
one component and the union of the other components. The terminals'
positive-even sets cover every off-terminal vertex except those at odd
distance from both. If there are odd-odd vertices on both sides, choose
one on each side: a cross-side distance between two odd-odd vertices
is the minimum of two even sums passing through the cut. Otherwise all
odd-odd vertices are on one side; use one port of each terminal on the
opposite side, selecting the nearer terminal for each remaining vertex.

Entry points in `Graffiti189LongestPath.CrossSaturation.TwoCutOrder`:
- `order_le_four_mul_add_two_of_actual_two_cut`.
- `order_le_twenty_six_at_six`.

Replay on Lean and Mathlib 4.19.0 with the checked earlier two-cut
bounds module `TwoCutOrderCenters189` on LEAN_PATH. Only standard
axioms appear in the axiom audit.
