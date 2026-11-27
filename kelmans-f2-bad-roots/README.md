# Kelmans: independent bad vertices for a fixed omitted edge

**Conditional partial result.** Assume the ordinary cyclically four-edge-connected cubic graph factor assertion at orders divisible by six. In a cubic, three-connected graph satisfying the cyclic-four cut condition and with order four modulo six, fix an edge to omit. Lean proves that vertices whose simultaneous deletion prevents a (P_3)-factor form an independent set. The fixed edge's endpoints cannot be bad.

For two disjoint handled edges, Lean also proves a fallback: if an endpoint of the second edge is bad in this sense, both old endpoints of that second edge can be removed while retaining the subdivision of the fixed edge in a graph with a (P_3)-factor. This does not rule out isolated bad vertices or prove F2 or the full Kelmans conjecture.

- [Independent bad vertices](src/CyclicF2Independent.lean)
- [Fallback with a retained subdivision](src/CyclicF2Alternative.lean)

In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/kelmans-f2-bad-roots/replay.sh`.
