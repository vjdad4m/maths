# Graffiti.pc #189: degree six, distance-three two-cuts through order 19

Two strict Lean results for an actual nonadjacent separator of distance
at least three at threshold six:

- If both shores have at most ten vertices, the graph is traceable.
  This includes the balanced 10+10 case, hence extends that branch
  beyond order 19.
- Shores of sizes six and eleven cannot occur. Their impossibility,
  together with the preceding result and the two-shore reduction,
  establishes traceability for every graph in this branch of order
  at most 19.

The six-vertex shore is forced to be a clique. Its opposite shore is
partitioned into the two marked port classes (each seen or unseen at
distance two from the other cut vertex) and four visibility classes
of nonports. The arithmetic contradiction follows from actual
distance-two and distance-four charges proved in the graph. The
computational diagnostics are not used in the Lean proof.

Main declarations in
`Graffiti189LongestPath.CrossSaturation.ThresholdSix`:

- `traceable_at_distance_three_two_shores_le_ten`
- `no_six_eleven_shores`
- `traceable_at_six_distance_three_order_nineteen`

All use only standard Lean axioms. The asymmetric larger profiles
beyond order 19 are not covered by this release.
