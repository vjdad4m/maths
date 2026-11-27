# Graffiti.pc #189: distance-two cuts into three components

Under the degree-five hypotheses of #189, a distance-two two-vertex cut leaves at most three connected components. If it leaves three, Lean proves one of them must be a singleton. The singleton bridges two other components of order six or seven. A spanning path with prescribed endpoint on each side then gives a Hamiltonian path for the whole graph. There is no graph-order assumption in the theorem. [Final distance-two theorem](src/DegreeFiveDistanceTwoThreeClose189.lean)

The package also rules out degree pairs (8,6), (8,7), and (8,8), in either order, at distance-three cuts under the same degree-five hypotheses. It uses two exact counts on the crossing and noncrossing sides. [Degree-pair exclusions](src/DegreeFiveEightSix189.lean) · [Earlier distance-three result](../graffiti-189-degree-five-cuts/)

This does not settle the two-component distance-two case or the general conjecture. In a prepared Lean/Mathlib 4.19.0 checkout, use `lake env bash /path/to/maths/graffiti-189-degree-five-more-cuts/replay.sh`. [Strict compiler transcript](StrictReplay.log)
