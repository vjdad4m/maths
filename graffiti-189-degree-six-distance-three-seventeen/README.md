# Graffiti.pc #189: degree-six distance-three cuts through order 17

For a finite connected graph remaining connected after every one-vertex
deletion, assume at most one vertex has degree below six and every vertex's
even-distance set has at most seven vertices, including itself. If the graph
has an actual two-separator at distance three and at most 17 vertices, then it
has a spanning path.

The preceding component-count result gives exactly two shores. Each has at
least six vertices and therefore at most nine. The all-high shore has local
minimum degree five because no vertex can see both cut terminals; the
fixed-terminal Ore theorem supplies a path between a port of each color.
The other shore, possibly containing the unique low vertex, has a spanning
path rooted at some port by the two-root Ore theorem. Join it through its
terminal, traverse the all-high shore, and end at the other terminal.

Both checked declarations are in
`Graffiti189LongestPath.CrossSaturation.ThresholdSix`:
- `traceable_at_two_small_shores_distance_three` (only assumes the two-shore
  premise and each shore of order at most nine, with no even-distance cap).
- `traceable_at_six_distance_three_order_seventeen`.

Run replay.sh with Lean and Mathlib 4.19.0 and the checked predecessor objects
on LEAN_PATH, notably the exact-two component package and the previous
fixed-terminal and two-root Ore path modules.
