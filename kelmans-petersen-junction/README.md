# Kelmans: centered cap modes and a Petersen junction

Lean verifies three distinct statements.

- **Centered cap modes.** Assuming the cyclically 4-edge-connected P₃-factor conjecture, a graph in that same class has a P₃-factor with any chosen root at the center of its path, using a specified incident edge as one of the two links. Consequently at least two different unordered pairs of links are achievable at each root. This does not assert all three pairs are achievable.
- **An unconditional obstruction to a stitching method.** On the marked Petersen core, none of the three possible single-loan attachments leaves a factor on the remainder when both residue-zero pieces are sealed. This is not a counterexample to Kelmans.
- **A conditional repair.** With the exact Petersen-core, cap, and attachment hypotheses in the proof, the centered mode gives a P₃-factor for the inflated graph without requiring vertex transitivity of the third cap. It still assumes the cyclic-four conjecture.

See [CenteredCapZ5.lean](src/CenteredCapZ5.lean), [CentralLeafObstruction.lean](src/CentralLeafObstruction.lean), and [PetersenJunctionZ5.lean](src/PetersenJunctionZ5.lean). The general conjecture remains open.

In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/kelmans-petersen-junction/replay.sh`.
