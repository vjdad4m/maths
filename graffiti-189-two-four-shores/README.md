# Degree-five #189 distance-two (2,4) two-shore profile

Scope: finite connected simple G and actual distinct components C,D covering all off-cut vertices, cut endpoints a,b at graph distance two, connected after every single deletion, all even-distance sets (counting center) of size ≤6, every distinct vertex pair has one degree ≥5, C has exactly two total ports and D exactly four. At least one common porter is required on C; none is assumed on D. Conclusion is a spanning path in the original graph. Does not claim (3,4) or an unrestricted conjecture solution.

New files in this directory, in serial module order:
- DegreeFiveFourForeignGeom189.lean 9cd1ff5ec5a5eab4e3d553fe062b7f75c4a549629eea0845da414c75afe3a231
- DegreeFiveTwoFourShapes189.lean 3b9bd8e0b948cf42afa1dcc88aaa453fa1c508e2c892a487f83c43ae647eb562
- RootedOreTwoCandidates189.lean 9419143836bd17a0d1d1c13a57f4d347e204952d9cd828cbb49e4c5356870fff
- DegreeFiveFreeOreSmallNear189.lean 2785b38303e9c24b2094edbaf24a6892a6897601a61fa4fcc0450d64b309d241
- DegreeFiveNearSixTerm189.lean d979cc39a55c81de6461188f0aeb2d962128269932c90926524bd90e33323bde
- DegreeFiveTwoFourClose189.lean 334d7aedc9d2e063999ddb4861eae786b5ddfca21c9339eb19ca2ebd7c6620f1

Prior dependency overlays: df618a6dd387d325befb15831bf74c85aca05e95 (including DegreeFiveThreeFiveShapes189) and bad6e514d00dd4f9538a48d8f05c6f547ee5c6ab (including DegreeFiveFourFourTerminal189, WingSignature189 and related actual-cut/Ore infrastructure). No predecessor changes.

Lean 4.19.0/mathlib 4.19.0 replay exited successfully, flags -j1 -s 65536 -DElab.async=false -DwarningAsError=true. All printed exactly [propext, Classical.choice, Quot.sound], including the namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut theorem traceable_of_actual_five_two_four_ports. Tool replay was a combined source audit ; these files preserve standalone modular imports and exact checked proof bodies. No enumeration, native_decide, custom axioms, or external write.

Method: four opposite ports almost fill a common porter's D₂ shell; D₄ can hold at most one vertex and eccentricity is at most four, since an inner layer would require two vertices. Own visible nonports are counted in both cut endpoint budgets. Tight charges force (|C|,|D|)=(6,≤6) or (7,4). In the first branch, two universal high nonports and at most one missing edge at the selected common give a prescribed-terminal path on C, while rooted Ore gives a free route on D. In the second branch, D is all ports and terminal, while the near-seven rooted Ore route on C only requires its two actual candidates. All spanning routes live in G after the auxiliary Ore completion is pulled back.
