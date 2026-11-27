# Kelmans: a conditional seven-vertex theta case

**Partial result.** Consider the six-cycle (0,1,2,3,4,5,0) with a seventh vertex (6) joined internally to (0) and (3). Label its five distinct exterior contacts in the order they attach at (1,2,4,6,5) by (p_0,ldots,p_4). In a cubic graph of order (4 pmod{6}) satisfying the exact cyclic-four and cyclic-five cut conditions, suppose neither (p_1p_4) nor (p_2p_3) is an exterior edge. The centered-neighbor cyclic z5 assertion then gives a (P_3)-factor after deleting vertex (6) and omitting edge (5!-!0).

The proof checks one prescribed three-vertex cap and transfers every possible tile through its retained leaf back to the six-vertex path. [ThetaCase.lean](src/ThetaCase.lean) gives the packing theorem. [ThetaGeometry.lean](src/ThetaGeometry.lean) shows when an adjacent exterior pair makes this particular cap fail; that is an obstruction to the route, not to F2.

The cap topology is based on the five-edge-shore completion of [Máčajová and Rajník](https://arxiv.org/abs/2107.09756). This result uses fixed port roles and does not claim novelty for the cap itself. General F2 and Kelmans remain open.

From a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/kelmans-theta-f2/replay.sh`.
