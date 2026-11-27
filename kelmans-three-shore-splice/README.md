# Kelmans: two exact three-shore splices

Assume the cyclically 4-edge-connected P₃-factor conjecture. Lean verifies full packings in two singleton-junction patterns where the three pieces, before adding their cap vertices, have orders modulo three of `(0,0,2)` or `(1,2,2)`. These theorems require explicit cyclic-four cap, partition, and attachment hypotheses.

- **`(0,0,2)`:** Pack the two residue-zero pieces internally. Use a [prescribed leaf edge](../kelmans-adjacent-avoidance) to pack the residue-two piece together with the junction vertex.
- **`(1,2,2)`:** Free a prescribed port on the residue-one piece. Use that port and the junction vertex to complete the two residue-two pieces.

See [RoutedK4Junction.lean](src/RoutedK4Junction.lean) for the precise hypotheses. These results do not assert that the compatible attachment patterns exist in arbitrary three-shore graphs or settle the Kelmans conjecture.

In a Lean and Mathlib 4.19.0 workspace, run `lake env bash /path/to/maths/kelmans-three-shore-splice/replay.sh`.
