# Graffiti.pc #180: exchanging vertices of the connected core

**Partial structural results.** The first-form certificate criterion compares with the original lower optimum, not a re-optimized trimmed lower score. Starting from a second-form certificate, Lean expresses the first form as an exchange of vertices of the connected dominating core that releases more eligible vertices than are returned.

- [A 12-vertex example](src/Example180.lean) shows that a specified second certificate can resist every single-vertex exchange. A two-vertex replacement succeeds; the example satisfies #180 with equality.
- [A 14-vertex example](src/AllTips180.lean) resists every single-vertex exchange even if the second certificate and its orientation can be chosen freely. A two-vertex replacement works from either orientation, and the graph satisfies #180.

These are obstructions to a particular proof strategy, not counterexamples to #180 or to the first-form criterion. We make no Lean-checked minimality claim for the examples. See [the core-exchange criterion](src/CoreSplit180.lean).

In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-180-core-exchanges/replay.sh` to rebuild the published chord criteria and all new modules.
