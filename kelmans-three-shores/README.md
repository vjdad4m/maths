# A conditional three-vacancy bound for Kelmans at exactly three minimal shores

The [Lean theorem](src/ThreeTerminalDomain.lean) concerns finite simple cubic 3-vertex-connected graphs of order divisible by six. If the cyclically 4-edge-connected case of the Kelmans P3-factor conjecture holds, then a graph with exactly three inclusion-minimal nontrivial shores of 3-edge cuts has a packing by three-vertex paths that leaves at most three vertices uncovered. A nontrivial shore here has at least two vertices on each side. The three shores need not be supplied with disjointness or internal edges: the formal proof derives both.

The [geometry](src/ThreeTerminalGeometry.lean) chooses three disjoint internal shore edges and steers two handle operations through them. The resulting host is cyclically 4-edge-connected and has four new vertices. Using the previously [proved conditional vertex-deletion lemma](../kelmans-domino-f1), remove one new vertex to obtain a factor of the punctured host. If the other three new vertices occupy at most two tiles, throwing those tiles away exposes at most three old vertices. If they occupy separate tiles, restoring one original edge joins four exposed old vertices into a four-vertex path, so a [local repair](src/ContactRepair.lean) fills one more tile and again leaves at most three vacancies.

The cyclically 4-edge-connected factor conjecture is an explicit hypothesis, not an imported axiom. This does not give an exact factor at three shores and does not settle Kelmans.

## Replay

From a Lean 4.19.0 project with the Mathlib 4.19.0 build cache:

    lake env bash /path/to/maths/kelmans-three-shores/replay.sh
