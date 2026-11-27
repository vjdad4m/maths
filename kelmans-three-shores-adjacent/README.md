# An adjacent vacancy pair in the conditional three-shore Kelmans packing

The [Lean theorem](src/ThreeTerminalAdjacent.lean) strengthens the [conditional three-vacancy bound](../kelmans-three-shores). Assume the cyclically 4-edge-connected case of the Kelmans P3-factor conjecture. For a finite simple cubic 3-vertex-connected graph of order divisible by six with exactly three inclusion-minimal nontrivial shores of 3-edge cuts, the proof yields either a P3-factor or a P3-packing leaving exactly three vertices uncovered, two of which are adjacent.

The proof follows the auxiliary-vertex tile cases of the earlier construction. It preserves an adjacent pair among exposed old vertices or replaces exposed tiles using one of the original restored edges. Divisibility rules out one or two uncovered vertices. This is not an augmentation theorem: the third vacancy is not necessarily adjacent to either endpoint of the pair. The full conjecture remains unresolved.

## Replay

From a Lean 4.19.0 project with the Mathlib 4.19.0 build cache:

    lake env bash /path/to/maths/kelmans-three-shores-adjacent/replay.sh
