# Graffiti.pc #384b: the lower diversity-eleven profile with independent ears

This package gives structural reductions, not a proof of the remaining diversity-eleven case.

Let G be a finite simple graph, and call vertices of degree at least three high. In a diversity-eleven counterexample with nine high vertices, any independent family of nonisolated low vertices has a high-neighbor footprint of size at least twice the size of the family minus one. Thus if all nonisolated low vertices are independent, there are at most five.

For a triangle-supported graph, assume vertices outside a finset H are independent and of degree at most two. Each high vertex's exact triangle count equals its count in G induced on H plus its number of neighbors outside H. Also every two-dominating witness can be shrunk to a canonical one specified by its retained subset S of H: retain S and every outside vertex not having degree at least two with all neighbors in S. Hence nine high vertices require only 512 retained-high choices per graph in this profile. No categorical claim about the adjacent-low case is made.

The numerical finite diagnostic is not part of this package. No brute-force coverage is asserted.

Replay with Lean 4.19.0 and pinned Mathlib v4.19.0. Put the earlier even-palette, diversity-eleven-structure, and upper-cubics object directories (in particular ShorePairs), with their transitive prerequisites, on LEAN_PATH. Run `lake env bash /path/to/this/package/replay.sh`. The only axioms reported are propext, Classical.choice, and Quot.sound.
