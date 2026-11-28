# Graffiti.pc #189: nonadjacent degree-six cut order bound

Assume a finite connected graph that stays connected after deleting one
vertex, with an actual cut pair and at most seven even-distance vertices
from any vertex (including itself). At distance two, its order is at
most 24: in the four-center cover each terminal already spends one
slot on the other terminal, which need not be covered.

For distance at least three, assume also all but at most one vertex
have degree at least six. The checked structural theorem gives exactly
two shores. In the four-center cover, every crossing reference then
spends one slot outside the shore it covers. An odd-odd reference
must have a local distance-two vertex: otherwise it is universal in
its shore, making it adjacent to both terminals. A terminal port either
has a local distance-two vertex, or is universal in its own shore; in
the latter case it sees the other terminal at distance two via a local
opposite port. Either event consumes an even slot outside the opposite
shore. Both crossing reference sets have size at most five after being
cropped to their covered shore, giving the same order bound 24.

The checked entry points in
`Graffiti189LongestPath.CrossSaturation.ThresholdSix` are
`order_le_twenty_four_at_distance_two` and
`order_le_twenty_four_at_distance_three`.

Run replay.sh using Lean and Mathlib 4.19.0, with the prior four-center,
exact-two, and short distance-three packages on LEAN_PATH.
