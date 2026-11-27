# Both-common degree-five distance-two (3,5) and (2,5) cuts

Scope: finite simple connected graph, actual cut with exactly two components (distinct CutGraph components whose shores cover all vertices outside the two cut vertices), cut vertices at distance two. For every vertex the set at even distance, including the vertex itself, has cardinality at most six; for every pair of distinct vertices at least one has degree at least five. Each shore has a common neighbor of the two cut vertices. If one shore has exactly five total cut ports and the other exactly three, also assume connectivity after any single deletion (the standard 2-connectivity hypothesis). If the other shore has exactly two ports, no single-deletion connectivity hypothesis is used. Conclusions in both cases: an original-graph spanning path. No claim for either remaining (3,4) or (2,4) or for one-port shores.

Exact source staging: all files below at this directory. Compile in order, after the public module dependency overlay from commit bad6e514d00dd4f9538a48d8f05c6f547ee5c6ab (Four-five shores), its public predecessors and terminal closure. The public overlay must include DegreeFiveBothNonsaturated189, DegreeFiveBothFiveResidual189, DegreeFiveBothFourFiveFifteenClose189, RootedOreExceptPair189, UniversalRouteSingletons189, WingSignature189, ResidualOreParam189 and DegreeFiveNearAllPortTerminal189. No prior module should be modified or copied to a new path.

- DegreeFiveThreeFiveDom189.lean 0614c6e9ab5f24ada8f8f28513fa5f0cc71f2627d65283d293d7f53259bc87af
- DegreeFiveThreeFiveBound189.lean 3728137a1e5dcf54b360b30e467a0cafb74ad175027db631bdd3098d4f6f6458
- DegreeFiveOppNonportFour189.lean 2848f4d1fc1507ae0395a21376ef138b08dd82858aedae6e1a9fc53e0f2f06b4
- DegreeFiveThreeFiveShapes189.lean 7da04ced7752cb65368a4cff89df95d17f0e7c839f78f0aae2e218237337fab4
- RootedOreMissingPair189.lean 76b72fd9be6060744188d41b771591403b9f7c257dbc98dcf1a2783a476351e5
- DegreeFiveThreeFiveFree189.lean d12a8371ff3a90abbe99563798cfdbb2786baa4bcfe22908641b43c0f4dd7e73
- DegreeFiveThreeFiveTerminal189.lean 67df6c94f709e1008e0c6143de479bbd0a41d2c16d150e34b113ee3c83199dc2
- DegreeFiveThreeFiveSeven189.lean 1cf8c8dd452e61b671e58c1a7b62feac18f9efae5555a06ae904550edf5f8f8a
- DegreeFiveThreeFiveAll189.lean e5efc4f5633f3f3d6fbec341389fee633271cb09f23e2ac9f54b2a1c5101f32a
- DegreeFiveOppositeFiveDoubleCharge189.lean 4c061845411535e7851867c5e2054d7956685153841be302ec5c20477dd2c7c3
- DegreeFiveTwoOrThreeTerminal189.lean 66c56039517cc958677ce73084d65b40618259fd172b5968c8cd925de17f4ff7
- DegreeFiveTwoFiveAll189.lean eac8fa26837175ef57de882aaa41020053205623c5702f84033897e7da23d8a8

Theorem namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut; final names traceable_of_actual_five_three_five_ports and traceable_of_actual_five_two_five_ports. Key geometry: a common porter on the small-port shore sees exactly the five opposite porters at distance two and has eccentricity at most three. Opposite nonporters must neighbor some opposite porter; own nonporters charge both cut endpoint budgets. This gives n+|C| ≤15+2|ports(C)|. In (3,5), cardinality possibilities are (4,≤8), (6,≤7), (7,5); when |C|=4 every D vertex is high, and a low nonporter in C sees all far nonporters at distance four. Original parity ensures every missing high-high pair on moderate larger shores is eligible for rooted Ore completion. The six-vertex small shore builds a terminal path using three universal vertices. Seven vertices use residual Ore after deleting just one common vertex. In (2,5) the shore orders are forced (6,5), since all nonporters in a shore of size at most five would be low.

Verification: combined strict Lean 4.19.0/mathlib v4.19.0 replay exited successfully with flags -j1 -s 65536 -DElab.async=false -DwarningAsError=true. Both final theorems list exactly [propext, Classical.choice, Quot.sound]. This was a combined synthetic source replay in the read-only build; standalone source files retain real module imports/open-private directives for independent serial compilation. Module header adjustments preserve the same checked proofs; the generalized double-charge print was corrected to its actual theorem name. All geometry and routes use the original graph except local Ore completion, whose path is explicitly transferred back. No sorry, extra assumptions, native_decide, finite graph enumeration or repository write.

