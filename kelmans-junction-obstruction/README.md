# Kelmans: a ten-vertex limit of the local junction argument

**Obstruction to a proof strategy, not to the conjecture.** Lean verifies the cubic, three-connected and cyclic-four properties of the explicit ten-vertex graph. Delete the independent marked vertices 0, 2 and 3. No single neighbor of root 2 can be deleted from the remaining core to leave a (P_3)-factor. The centered junction geometry is feasible for exactly one unordered pair of neighbors: ({5,9}). Thus this local argument cannot rely on a single-neighbor loan, and knowing only that two of three pairs are available in a different graph need not hit the uniquely feasible pair.

- [Obstruction and exact pair](src/Z5JunctionGap.lean)
- [Ambient graph hypotheses](src/Z5JunctionGapGeometry.lean)

In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/kelmans-junction-obstruction/replay.sh`.
