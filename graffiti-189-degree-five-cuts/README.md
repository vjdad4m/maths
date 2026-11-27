# Graffiti.pc #189: degree-five two-vertex cuts

**Partial results, Lean-verified.** For the degree-five hypotheses of #189, a two-vertex cut in a 2-connected graph has its two vertices at distance at most three, and a distance-three cut leaves exactly two components. A spanning path exists when both components have order at most seven. [Actual-cut distance](src/DegreeFiveActualCut189.lean) · [Small-side theorem](src/DegreeFiveSmallActual189.lean)

**Every distance-three cut whose two vertices both have degree exactly five is traceable under the #189 hypotheses, with no side-size or attachment-count restriction.** The balanced and 2+2 / 3+3 profiles use prescribed-endpoint wing routes, proved separately and joined without altering the original graph. The remaining 4-port cases use tight parity shell bounds. [Actual-cut theorem](src/DegreeFiveExactDistThreeActual189.lean) · [Split theorem](src/DegreeFiveExactDistThree189.lean)

The remaining degree-five configurations and the unrestricted conjecture remain open. For the completed degree-four case, see [the earlier package](../graffiti-189-complete-degree-four/).

In a prepared Lean/Mathlib 4.19.0 checkout, run `lake env bash /path/to/maths/graffiti-189-degree-five-cuts/replay.sh`. The script rebuilds the public dependencies, verifies the exact input hashes, and checks the new source. [Strict compiler transcript](StrictReplay.log)
