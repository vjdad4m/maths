# Graffiti.pc #189: order bound for every degree-five counterexample

For a connected finite simple graph with at most six even-distance vertices at each vertex (including the vertex itself), and all but at most one vertex of degree at least five, any counterexample to traceability has at most 17 vertices. Equivalently, every such graph of order at least 18 has a Hamiltonian path.

The degree-five reduction supplies connectivity after deleting fewer than two vertices and an adjacent pair whose deletion disconnects the graph. Above order 17 the deleted graph is nonempty, so it has at least two components. The exact-three exclusion gives exactly two components; the adjacent exact-two upper bound then contradicts order at least 18.

Declarations: Graffiti189LongestPath.order_le_seventeen_of_degree_five_counterexample and Graffiti189LongestPath.traceable_at_degree_five_of_order_eighteen. This does not settle the low-order residue or other degree thresholds of Graffiti.pc #189.

Strict Lean 4.19.0, one compiler thread; asynchronous elaboration disabled; warnings as errors; both declarations rely only on propext, Classical.choice and Quot.sound. Direct dependencies: DegreeFiveReduction189, AdjacentCutFiveTopFlatten189, AdjacentCutFiveThreeExactViaCombinator189.

[Top-order profile proof](PROFILES.md) and [Lean check](LEAN-CHECK-PROFILES.txt). The final [counterexample cap](ThresholdFiveCounterexampleOrder189.lean) also uses the [adjacent-cut reduction](../graffiti-189-degree-five-reduction/) and [exact two-shore theorem](../graffiti-189-adjacent-exact-two-shores/). Compile in the supplied order after those dependencies.
