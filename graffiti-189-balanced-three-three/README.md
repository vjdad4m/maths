# Graffiti.pc #189: balanced common shore versus a two-three exclusive shore

for the Graffiti.pc #189 degree-five premises at a two-component distance-two 2-vertex cut, the graph has a spanning path if one component has three contacts to each cut vertex with at least two common contacts, and the opposite component has only exclusive contacts, two to the first and three to the second. The exact common-shore profile forces a four-vertex common component and a low nonporter. General #189 remains open.

The Lean theorem is `traceable_of_balanced_three_three_opposite_two_three`. Exact source hashes are in `sources.sha256`.

## Replay

Use pinned Lean and Mathlib v4.19.0. First put the compiled objects for the following dependencies, including their own imports, on the Lean search path:

- graffiti-189-degree-five-cuts: DegreeFiveActualCut189, DegreeFiveRouteBasic189, DegreeFiveFourPort189, DegreeFiveDistanceTwoComponents189, DegreeFiveDistanceTwoThreeClose189, DegreeFiveDistanceTwoSingletonClose189.
- graffiti-189-unique-exclusion: DegreeFiveThreeForeignImpossible189.
- graffiti-189-distance-two-twenty: DegreeFiveExclusiveGateway189.
- graffiti-189-closure-test: DegreeFiveUniquePortClosureTest189, DegreeFiveUniquePortHighShore189.
- graffiti-189-closure-full: DegreeFiveFourForeign189, DegreeFiveUniquePortLowCommon189, TerminalOreClosure189, TerminalOutlier189.
- Eight-terminal stage: DegreeFiveOppositeEight189, DegreeFiveEightTerminalShore189.


The eight-terminal package is [here](../graffiti-189-eight-terminal/). Compile these new modules in `modules.txt` order, with `-j1 -s 65536 -DElab.async=false -DwarningAsError=true`, adding newly built objects to the Lean search path. The recorded end-to-end replay succeeded under exactly propext, Classical.choice, and Quot.sound.
