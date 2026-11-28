# Graffiti.pc #189: degree-six distance-three two-cuts through order 20

The distance-at-least-three actual two-cut branch of #189 is traceable
through order 20. This closes the remaining 6+12 shore split after the
separate 7+11 result; balanced shores of size at most ten were already
covered. No claim is made for orders 21–24 or for the full conjecture.

The six-shore is a clique. The preceding frontier theorem excludes
wholly hidden vertices in the larger shore and all vertices are assigned
to seven terminal-visibility buckets. Exact degree, visibility and
external even-distance bounds restrict the bucket counts to 53 normalized
profiles. Role-preserving relabeling sends the possible single degree
exception to the profile's marked position. For each profile, Lean
constructs an adjacency and ambient-D2 valuation of a finite formula.
A checked ASCII LRAT derivation refutes that formula. It requires only
D2 lower clauses (two-edge walks force adjacency or distance two), not
a shortest-distance solver or internal higher shells. The certificate
checker and all graph statements run in Lean with standard axioms only.

Main theorems:
- Graffiti189LongestPath.CrossSaturation.ThresholdSix.no_six_twelve_shores
- Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_at_six_distance_three_order_twenty
