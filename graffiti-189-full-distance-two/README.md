# Graffiti.pc #189: all distance-two cuts at the degree-five threshold

**Exact Lean result for this branch.** Let G be a finite, connected,
simple graph that stays connected after deleting any one vertex.
Suppose each vertex has at most six vertices at even distance, counting
itself, and for each pair of distinct vertices at least one has degree
at least five. If two vertices at graph distance two form a vertex cut,
then G has a Hamiltonian path in the original graph.

There is no order limit, and no condition on how many components the
deletion leaves, or on which cut vertex hits which vertices within a
component. The theorem splits the actual cut into three-or-more and
two-component cases. The latter combines both-common and exclusive-shore
proofs. No graph edges are silently added in the conclusion.

The exact theorem is
`Graffiti189LongestPath.CrossSaturation.FiveActualCut.traceable_of_actual_five_distance_two_cut`.
Both it and the two-component theorem passed a serial Lean 4.19.0
kernel replay with only the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`. The replay included all 161
modules in the integration package. The 1+4 port case uses a singleton
shore, a graph order bound of 11, and the unrooted Ore closure threshold.

[Exact statement and proof](DegreeFiveDistanceTwoAll189.lean) ·
[One/four Ore closure](DegreeFiveOneFourClose189.lean) ·
[Strict verification](StrictReplay.log) · [Pinned baseline sources](PINNED-BASELINES.tsv)

## Replay

Extract the archive below. Build the pinned baseline packages on Lean
4.19.0 (6caaee842e94) and Mathlib v4.19.0
(c44e0c8ee63ca166450922a373c7409c5d26b00b), with their object roots
on LEAN_PATH, and run `lake env bash /path/to/replay.sh`.
`external.txt` lists the required baseline object names; their
source paths and Git blobs are pinned in `PINNED-BASELINES.tsv`.
The harness verifies the exact bundled source hashes and performs
a fresh modular replay. `PATCHES.tsv` distinguishes upstream
module-only changes from the new dispatcher count and 1+4 proof.

Unrestricted #189 remains open here. In particular this does not
settle cuts at other distances or eliminate counterexamples without
a distance-two separating pair.

[Complete pinned Lean sources](proof-sources.tar.gz). Extract the archive and use its replay script.
