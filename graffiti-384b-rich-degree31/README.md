# Graffiti.pc #384b: diversity 31 with thirty vertices of degree at least three

Lean proves the inequality for every connected finite simple graph with exactly 31 distinct triangle-incidence counts and exactly 30 vertices of degree at least three, with no restriction on total order. A proof using a protected cut through a five-clique forces a cubic neighbor at every clique vertex in a putative counterexample. Counting these contacts rules out a seven-clique and then excludes the exceptional triangle counts through degree nine. [Main theorem and exact residual](CoverDense31.lean)

Any remaining connected counterexample at diversity 31 has exactly 29 vertices of degree at least three. Their counts are pairwise distinct and at least two. The degree-three-vertex count here is distinguished from the graph's total order. This is not a solution of the general conjecture.

Replay with the pinned Lean/Mathlib 4.19.0 and the settings from the [prior package](../graffiti-384b-five-clique-free31/): run `bash replay.sh`. [Strict compiler transcript](Strict244.log)
