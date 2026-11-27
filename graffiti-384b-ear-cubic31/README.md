# Graffiti.pc #384b: the diversity-31 adjacent ear–cubic case

**Partial result.** If a finite connected five-clique-free graph has exactly 31 distinct vertex triangle counts and a triangular degree-two vertex adjacent to a vertex of degree at most three, then its 2-domination number is at most its order minus 16, as predicted by #384b. [Lean proof](SevenFinish.lean)

The [prior pivot theorem](../graffiti-384b-diversity31/FrontierPivot31.lean) forces two overlapping diamonds in a seven-vertex configuration. Lean verifies both this configuration and a sampler selecting eight of the 23 vertices outside it. A remaining five-clique-free counterexample at diversity 31 must have both neighbors of the unique ear of degree at least four in its core. The remaining diversity-31 cases and the full conjecture are open.

For the public dependency replay run `bash replay.sh` with the same Lean/Mathlib v4.19.0 and `CROSSFOUR_LEAN_BIN` and `CROSSFOUR_MATHLIB` settings as the [prior package](../graffiti-384b-diversity31/). [Strict compiler transcript](Strict233.log)
