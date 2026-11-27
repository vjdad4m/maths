# Graffiti.pc #133: sparse four-point attachment patterns

These Lean 4.19 results bound the average local independence by four in several configurations not covered by the [two-edge attachment result](../graffiti-133-four-palette/). A core is a connected dominating induced subgraph with no induced seven-vertex path. The four attachment points in the core cover all edges from the exterior.

- [One edge, unique exterior attachments](src/P5CliqueSingleEdgeSingletonClosure133.lean): if the ambient graph has no four-cycle or induced nine-vertex path, the bound holds at **every** core order. The proof combines a fan count with a [separate small-core inequality](src/P5CliqueSmallCoreSignedSlack133.lean).
- [One edge, arbitrary exterior attachments](src/P5CliqueSingleEdgeMultiBudget133.lean): the bound holds for core order at least 17, or when the exact core slack pays the stated number of extra attachments. Smaller multivalent cases are not all covered.
- [Four attachment points with a common core neighbor](src/P5CliqueFourRelayRadiusFour133.lean): in the same ambient forbidden-subgraph class, radius at least four suffices. No additional degree or slack assumption is made.
- [Three points with a near-common core neighbor](src/P5CliqueFourNearThreeRadiusFour133.lean): a related conclusion for an independent palette, unique attachments, and a core vertex adjacent to at least three of the four points and within two of all four.
- [A clean induced six-vertex path](src/P5CliqueFourCleanP6Budget133.lean) and [the four-leaf minimum tree core](src/P5CliqueFourLeafMinimumTree133.lean): the former uses unique attachments and a path in the core with two attachment endpoints and the other two off the path. The latter proves the needed path in the stated radius-four tree-core configuration.

The full conjecture remains open. The sources passed strict Lean 4.19 replays with standard axioms. With pinned Mathlib and the prerequisite objects from [the previous four-point package](../graffiti-133-four-palette/) on the Lean search path, compile the source modules in `modules.txt` order. Their hashes are in `sources.sha256`.
