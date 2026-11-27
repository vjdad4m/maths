# Graffiti.pc #133: size of a dominating seven-cycle core

**Structural partial result.** In a finite graph with no ordinary four-cycle and no induced seven-vertex path, suppose an induced seven-cycle dominates the graph. Lean proves that the off-cycle vertices form an independent set and the graph has at most ten vertices. If the graph is connected and has radius at least three, Lean improves this to at most nine vertices.

The proof classifies the possible contact masks at the cycle and tests the pair constraints. Every compatible triple of outside masks gives a cycle vertex at distance at most two from every vertex in the resulting ten-vertex graph, eliminating the order-ten case at radius three.

This bounds the size of one possible inner dominating core in the radius-four mean-five analysis. It does not prove a bound on the full graph or settle that residual branch. See [the exact Lean theorems](src/C7CoreOrder133.lean). The included generator constructs witnesses; Lean checks them.

From a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-133-c7-core/replay.sh`.
