# Graffiti.pc #189: adjacent separating pair with two shores

Assume the finite simple graph is connected and remains connected after deleting fewer than two vertices. The cut vertices are adjacent, and deleting both leaves exactly two connected components. At every vertex, at most six vertices (counting the vertex itself) are at even distance.

* The order is at most **19**, with no degree assumption (AdjacentCutFiveTwoDoubleCover189, order_le_nineteen_of_actual_adjacent_two_shores). The preceding bound 20 is independently checked and gives a simpler proof stage.
* If the terminals are true twins and order is at least 17, the graph is traceable (AdjacentCutFiveTwoTwinSeventeen189, traceable_of_order_seventeen_adjacent_twin_two_cut). The existing twin bound makes this exactly the order-17 case. No degree hypothesis is needed here either.
* The general adjacent two-component low-order case and Graffiti.pc #189 are not resolved by this package.

The upper bound treats the four positive even-distance covers as two terminal sets and two opposite-shore port sets. Two overlaps force saturation at order 20. A port center with five positive even vertices across the cut is universal on its own shore: any local shortest route to a nonneighbor would hit a local distance-two vertex. For the order-17 true-twin case, this forces five universal ports per shore; remaining vertices are joined as singleton blocks, and the shore paths are linked by the edge between the cut terminals.

Lean 4.19.0, warnings as errors, serial and asynchronous elaboration disabled. The new source modules are built in order.txt order. Dependencies are the existing adjacent structure sources (AdjacentCutFiveBound189, AdjacentCutFiveActual189, AdjacentCutFiveComponents189) and degree-five/distance-two universal route sources. LEAN-CHECK.txt contains the consecutive strict verification excerpts for the frozen declarations. Each listed theorem relies only on propext, Classical.choice and Quot.sound.
