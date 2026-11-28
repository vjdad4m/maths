# Graffiti.pc #189: every threshold-five counterexample has order at most 16

A connected finite simple graph with at most six vertices at even distance from each vertex (including itself), and at most one vertex of degree below five, has a Hamiltonian path if its order is at least 17.

At order 17, the compact six-class parity arithmetic shows that the smaller shore of a genuine two-shore adjacent cut is either a four-vertex equal-odd shore, or both shores have no exclusive-nearer classes. The first option is impossible by the four-common-shore bound. The second forces adjacent true twins, and the previously checked true-twin route gives a Hamiltonian path. Thus a genuine two-shore adjacent cut with unequal terminal neighborhoods has graph order at most 16. The global threshold-five reduction and the exact-two-components theorem then give the global order bound.

Main declarations: Graffiti189LongestPath.order_le_sixteen_of_degree_five_counterexample, Graffiti189LongestPath.traceable_at_degree_five_of_order_seventeen. The actual adjacent unequal cutoff is Graffiti189LongestPath.CrossSaturation.FiveAdjacent.order_le_sixteen_of_actual_adjacent_two_unequal_shores. This does not resolve the lower order residue or other degree thresholds.

Lean 4.19, single-thread serial replay, warningAsError=true, asynchronous elaboration disabled. All six terminal axiom reports list only propext, Classical.choice and Quot.sound. Replay order.txt. Direct external modules: AdjacentCutFiveTopArithmetic189, AdjacentCutFiveTopFlatten189, AdjacentCutFiveTwinFourteen189, DegreeFiveReduction189, AdjacentCutFiveThreeExactViaCombinator189, together with their transitive dependencies.
