# Degree-five #189 distance-two (3,4) two-shore profile

Scope: finite connected simple G with actual distinct components C,D covering all off-cut vertices, cut endpoints a,b at graph distance two, graph connected after every single deletion, all even-distance sets (counting the center) of size ≤6, every distinct vertex pair has one degree ≥5, C has exactly three total ports, and D exactly four. A common porter is required on C only; none is assumed on D. Conclusion: an original-graph spanning path. No general #189 claim.

Compile the six sources from the [2+4 release](../graffiti-189-two-four-shores), then the seven sources in this directory in this order:
- DegreeFiveFourForeignTight189.lean b2f3af9ea3779bb4886978166ee372c45db5f6c40e81bc31fe9a54328d3f6281
- DegreeFiveThreeFourShapes189.lean 7838745a9504c4bea2c42250fa017fd8fcf53058e567d84b90485173bc61b98a
- DegreeFiveFreeOreThreeForeign189.lean f8ab9c158d265f05da17b7ab04514c4d0e96a27f2d7994d6188106b799800407
- CliqueLowInsert189.lean 533cf0b9e63b21149ae5c7a6012fb888f9eb13ceb11b7e0f38f03ad4c993ab37
- DegreeFiveNearSevenTerminal189.lean c4cb7963855fbe84fe35399204a5e5ee81aca298a0a439e82c3a22618efa4bc8
- DegreeFiveFourSmallTermGeneric189.lean f511c3e123240dba23480a741721efa016b11cf5fcc1eeacd57100db13d52333
- DegreeFiveThreeFourClose189.lean 3f66b77721bbd832ef6549de0968bf8896fba392082ba786717b8940e52d34a7

Use modular predecessor overlays as in the 2+4 release, including df618a6dd387d325befb15831bf74c85aca05e95 and bad6e514d00dd4f9538a48d8f05c6f547ee5c6ab. Strict combined source replay exited successfully with flags -j1 -s 65536 -DElab.async=false -DwarningAsError=true, Lean/Mathlib 4.19.0. All printed exactly [propext, Classical.choice, Quot.sound], including final Graffiti189LongestPath.CrossSaturation.FiveActualCut.traceable_of_actual_five_three_four_ports. No finite enumeration, custom axioms, sorry, native_decide, or push. The validation replay concatenated sources; the frozen standalone files preserve module and private opens for independent modular verification.

Geometry: two endpoint charges per own visible nonporter and at most one exceptional foreign nonporter produce (C,D) size branches (4,≤8 all-high), (6,≤7 or ≤8 all-high), (7,≤6), and (8,4). Tight total charge excludes every porter neighbor of the missed own nonporter, exposing its low degree when needed. At (7,5/6) any low C-vertex is a nonporter and has two internal neighbors. Complete high-high missing edges with terminal Ore and insert the low vertex between those two high neighbors, choosing terminal ports to avoid a two-endpoint obstruction. Other branches use finite-order structural Ore eligibility and original-graph route masks. At D4 bridge the two actual cuts with D's terminal route and a free route on C. No ambient parity calculation after any auxiliary edge addition.
