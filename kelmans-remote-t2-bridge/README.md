# Kelmans: remote-deletion bridges and cyclic-five completion

This is a partial result, not a proof of the Kelmans conjecture or the remote-deletion variant.

- The graph left after deleting an adjacent pair and then an extra surviving edge has at most one bridge with two nonsingleton sides in the cyclic-four domain. With the stronger cyclic-five premise, no such bridge survives. See [the cut argument](src/RemoteT2NontrivialBridge.lean).
- If a leaf bridge and a nonsingleton bridge coexist, the leaf-side shore of the latter is a two-vertex path. In any factor the leaf and that path force the exact three-vertex tile specified by [the factor equivalence](src/RemoteT2LeafBridgeFactor.lean).
- In the cyclic-five domain, [the automatic same-side completion](src/RemoteT2CompletionTransfer.lean) has two fewer vertices, is cubic and cyclic-four, and allows an exact factor lift **if all three specified edges are avoided**. One specified edge is disjoint from both others. Ordinary two-edge avoidance alone is insufficient; the smaller isolated-edge-pattern three-avoidance statement remains unproved.
- A conditional [zero-residue shore theorem](src/RemoteT2ZeroShore.lean) instead uses strictly smaller ordinary adjacent-pair deletion when the specified four-port cap decompositions are available.

The [modular replay log](StrictReplay.log) uses Lean 4.19.0 and Mathlib 4.19.0, with warnings as errors and only standard axioms. To rebuild from the repository, run `lake env bash /path/to/maths/kelmans-remote-t2-bridge/replay.sh` from a prepared Mathlib checkout.
