# Graffiti.pc #384b: two triangular ears at order 34

**Partial result.** Let a finite simple graph on 34 vertices realize 33 distinct triangle-incidence counts. If two distinct degree-two vertices each lie in a triangle, the graph has a 2-dominating set of size at most 17. Connectedness is not required.

This covers both the four-anchor path and triangle-with-pendant configurations left by the earlier order-34 analysis. In a hypothetical failure, the proof identifies an ear with a unique common neighbor on its anchor edge, and uses a matching bound in one anchor's neighborhood. Keeping both endpoints lets the sampling argument omit the ear and count a further omission when the other ear's two anchors are sampled. Lean verifies the finite profile estimates as well as the graph argument.

See [the two-ear theorem and the exact remaining one-ear reduction](src/CrossFour34_384b.lean). In the normalized least-order counterexample analysis, order 34 now forces exactly one degree-two vertex. Smaller orders and the full conjecture remain open.

The proof reuses [the previous order-34 package](../graffiti-384b-order34/README.md). Run `CROSSFOUR_MATHLIB=/path/to/mathlib4 CROSSFOUR_LEAN_BIN=/path/to/lean/bin bash replay.sh` to verify the previous source hashes and rebuild both the inherited and new modules under Lean 4.19.0.
