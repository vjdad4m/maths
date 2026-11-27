# Graffiti.pc #133: exact mean at path order six

For a connected finite simple graph with no cycle of length four, if every induced path has at most six vertices, the exact mean of the independence numbers of the induced neighborhoods is at most three. No radius, edge-count or maximum-neighborhood-independence hypothesis is needed. The proof uses the [seven-vertex induced path theorem](../graffiti-133-induced-seven/) and the verified equivalences with the usual list and neighborhood-independence definitions. [Lean](PathSixBridge.lean).

This mathematically implies the [Left to Solve radius-three step](https://lefttosolve.com/p/WrittenOnTheWallII.GraphConjecture133.conjecture133.R1.H1.R1.H2.R1.H1). This file was checked under Lean and Mathlib 4.19.0 with warnings as errors; only propext, Classical.choice and Quot.sound appear in the axiom report. The external checker uses a newer pinned toolchain and its own graph-invariant declarations; this file does not claim external acceptance. The full #133 remains open.

To replay, first build the induced-seven package and its documented dependency chain on Lean 4.19.0 and Mathlib v4.19.0. With their build objects on the Lean search path, run `sha256sum -c sources.sha256` then `lean -DwarningAsError=true PathSixBridge.lean`.
