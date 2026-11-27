# Avoiding two disjoint edges in the cyclic-4 Kelmans class

**This is an equivalence, not a proof that the packings exist.** On finite simple cubic 3-vertex-connected graphs of order divisible by six with cyclic edge-connectivity at least four, the ordinary universal $P_3$-factor claim is equivalent to the universal claim with the added requirement that two prescribed edges sharing no endpoint are avoided. The statement and its converse are checked in [HandleFactor.lean](src/HandleFactor.lean), theorem `cyclic_two_edge_avoidance_iff`.

The forward implication turns the two prescribed edges into an adjacent pair of deletable vertices. Subdivide both edges once and join the new vertices. The new graph has two more vertices, is cubic, and is still cyclically 4-edge-connected. To check the last property, project a cut of size at most three back to the old vertices. A subdivided edge contributes at least as many crossings as the original edge, so the old cut has at most three edges and one old shore contains at most one vertex. A nontrivial new shore cannot consist of only the two new vertices, since their boundary has size four. If it contains exactly one old vertex, its old boundary already contributes three, and adding either new vertex (or both) contributes at least one more. The disjointness of the prescribed edges is used here. The package also checks the new graph's 3-vertex-connectivity and proves that deleting the new pair recovers exactly the old graph minus the prescribed edges.

Apply the [adjacent-pair deletion reduction](../kelmans-affine-t2) to the new graph. The reverse implication selects any two disjoint edges and retains the resulting factor in the original graph.

Kelmans uses an analogous subdivision in [§3.16 of *Packing 3-Vertex Paths in Cubic 3-Connected Graphs*](https://arxiv.org/abs/0910.2766) for the unrestricted domain. The Lean proof here verifies preservation of the cyclic-4 restriction and transfers the packing with that restriction. No claim is made for a pair of edges sharing an endpoint or for preservation of a fixed girth threshold.

## Replay

From a Lean 4.19.0 project with the Mathlib 4.19.0 build cache:

    lake env bash /path/to/maths/kelmans-handle/replay.sh
