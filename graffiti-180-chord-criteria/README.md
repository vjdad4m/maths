# Graffiti.pc #180: certificates for a triangle-chord step

**Partial result.** In the one-edge step that adds a chord across a two-edge path, Lean proves an exact test for the two-component certificate: after erasing eligibility of both chord endpoints, the upper graph must still improve on the original lower optimum of weighted spanning-tree leaves.

This certificate is forced under the stated tightness and rank-drop hypotheses when the lower graph is bipartite, and in a second case where its parity-crossing edges contain a spanning cycle and the chord endpoints have equal root depth at least two. This verifies the lower-to-upper step only under the hypotheses in the sources, not the whole conjecture.

- [Exact certificate criterion](src/FirstForm180.lean)
- [Bipartite lower graph](src/TightFirst180.lean)
- [Parity-crossing spanning cycle](src/CycleFirst180.lean)

The dependencies are included as plain Lean source. From a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-180-chord-criteria/replay.sh`.
