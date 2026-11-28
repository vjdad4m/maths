# Degree-five Graffiti.pc #189: impossibility of the (2,3) distance-two cut profile

Strict theorem Graffiti189LongestPath.CrossSaturation.FiveActualCut.impossible_actual_five_two_three_ports, concluding False. Assume finite connected simple graph, actual two distinct components of deleting a,b cover all off-cut vertices, distance(a,b)=2, graph stays connected after any single deletion, each even-distance set including the center has size ≤6, and every distinct vertex pair includes at least one vertex of degree ≥5. The two components have 2 and 3 total contacts with the cut, respectively. No shared-contact assumption and no graph-order cap.

Dependencies: after earlier public (1,5) source overlay for DegreeFiveOneFiveFarProfile189 (the private nonport shell equivalence), (3,4)/(2,4), DegreeFiveActualCutSwap189 and actual-cut/Mathlib predecessors. All new exact files are in this package, in serial order below:
- DegreeFiveTwoThreeBase189.lean 61f99991f3a54f023e6c6a603f20bf3c8126813b06b976552fb2081efa8cdf05
- DegreeFiveTwoThreeVisTwo189.lean 65d7a4c9fb0556e74012379744c3d2c0d963f042a41b31cb11fb65f547d61088
- DegreeFiveTwoThreeVisThree189.lean 6908989da4242253a39cb4d4c7baf7c423718dd9867d8828d13a7b0fe2277a30
- DegreeFiveTwoThreeClose189.lean c956dc19c9cd0c19795a2158ed7701e328513108d4f86d292a202fd949df4c76
- DegreeFiveTotalPorts189.lean 6c5d052c4ce1b72a07970a11b76bd54b49716de518cbafe1d14404451196cfe6

Optional last module also establishes five_le_total_ports_at_distance_two under only distance-two actual covering cut and pair-degree hypothesis. In particular all two-component profiles with total contacts below five are impossible even without parity or single-deletion hypotheses.

Lean/mathlib 4.19.0 exact read-only synthetic source audit combined source replay exited 0 under -j1 -s 65536 -DElab.async=false -DwarningAsError=true. Both case branches, final contradiction, and total-contacts bound printed exactly [propext, Classical.choice, Quot.sound]. Frozen standalone modules retain actual dependency imports and private opens for serial independent replay. No enumeration, sorry, native_decide, custom axioms, or writes to the repository by this worker.

Proof: at least one cut vertex has degree≥5 and hence touches all five porters. Its four off-cut distance-two slots give the two-port shore two or three visible nonporters, and it has at least one dark nonporter. With two visibles, a high porter must see both; the first dark fringe has size exactly two, and a high fringe vertex forces ≥2 vertices in the next layer, violating the even budget. With three visibles, the other shore is order four, its unique nonporter is low, and the two-port shore is all-high. The high cut's even budget is already spent, so all dark are in the first dark fringe. Each porter sees at most two dark at distance two. Three dark vertices must all see every visible, impossible; four dark vertices force disjoint two-vertex dark sets for the two porters, and ≥2 visible neighbors of each color, although there are only three. Excludes both cases.
