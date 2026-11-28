# Graffiti.pc #189: degree-six distance-three cuts through order 18

The earlier order-17 proof handles all cases except one shore of order 10
and the other of order 6. If the larger shore contains the possible
low-degree vertex, it supplies the rooted free route while the smaller
all-high shore connects the two terminals. Otherwise the larger shore is
all-high and must be routed between its two distinct terminal-port classes.

Its local minimum degree is five. If all local degrees were exactly five,
all ten vertices would be exclusive ports. Each color is capped at six.
The endpoints of a local edge between opposite colors each see four local
nonneighbors and the opposite terminal at distance two. This leaves at most
one same-color port in the six-vertex shore. Each color in the ten-vertex
shore has at least two vertices that bridge to the other color: if it had a
unique bridge, the other vertices of that color would force five same-color
neighbors for the bridge, which also needs a neighbor of the opposite color.
At least one of the two unique ports in the small shore is high and forces
five local distance-two neighbors of its terminal, contradicting those
two bridge slots. Thus the large shore has a local degree of at least six.

A weighted terminal Ore closure turns this into a path between ports of
opposite colors. Make one local degree-six vertex universal. If any degree-five
vertex remains, it is a port. Choose it as the prescribed end and choose the
start in the opposite class. The new edges at the prescribed end qualify
at sum 10 rather than 11, by adjoining its final pendant leaf before applying
rooted closure. Making it universal raises all four of its former nonneighbors
to degree at least six. Those four plus the first universal vertex and
the chosen end give six vertices whose new incident edges all satisfy ordinary
terminal Ore; completing their stars then gives local minimum degree six.
Pull back the spanning path through the three valid closure steps.

Main declarations in `Graffiti189LongestPath.CrossSaturation.ThresholdSix`:
- `weighted_terminal_ore_closure`
- `cross_marked_ten_ore`
- `traceable_at_six_distance_three_order_eighteen`

Replay with Lean and Mathlib 4.19.0, with the previous order-17 distance-three
package, exact-two components, and previous cut and Ore modules on LEAN_PATH.
Axiom reports contain only propext, Classical.choice and Quot.sound.
