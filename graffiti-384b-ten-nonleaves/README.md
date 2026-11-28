# Graffiti.pc #384b: the ten-nonleaf case at diversity nine or ten

For every finite simple graph with exactly ten vertices of degree at least two and nine or ten distinct triangle-count types, the catalogue two-domination inequality holds. The graph need not be connected. This result does not settle the outstanding eleven- and twelve-nonleaf diversity-nine cases or the unrestricted conjecture.

Main theorem: `Graffiti384b.Q10.exact_of_ten_nonleaves` in [Q10Exact384b.lean](src/Q10Exact384b.lean).

## Proof

1. All triangles lie in the nonleaf core. The original graph's type diversity therefore implies at least eight distinct **positive** triangle counts on its ten-vertex core.
2. Representatives of the two largest distinct counts have scores at least seven, hence core degrees at least five. Five common neighbors immediately give five vertices to omit. Otherwise the two anchor neighborhoods have one of twenty-nine contact shapes after relabeling the other eight vertices. The adjacent degree-five anchors with four common neighbors are true twins, so their exact triangle scores agree and they cannot represent distinct values. Lean proves this equality symbolically for every assignment of the free edges.
3. The remaining twenty-eight candidate edges are covered by an explicit finite decision tree per remaining shape. A leaf either certifies a retained set of at most five or excludes that leaf using a score lower bound, the two-anchor rank property, redundant scores, or a pigeonhole interval for possible scores. In the two-anchor rank test, any other score at least the smaller anchor score equals one of the anchor scores. Three such other vertices would be redundant and leave at most seven positive types.
4. In a witness, each omitted vertex has either two retained neighbors on the core or no omitted neighbor there. In the second case every ambient neighbor is kept, and a nonleaf has at least two ambient neighbors. Thus the witness lifts to the exact original inequality.

The certificate data consist of Boolean decision trees with a proved soundness theorem. Lean checks them using constructive `decide`; no external solver, `native_decide`, or unchecked oracle is used. The unrelated exploratory SAT experiment is not a dependency.

## Replay

Use Lean 4.19.0 (6caaee842e94) and Mathlib v4.19.0 (c44e0c8ee63ca166450922a373c7409c5d26b00b). Build the baseline, diversity-29, and nine-nonleaves bundles first, retaining their compiled objects and Mathlib dependencies on `LEAN_PATH` (the imported local modules are `Proof384b` and `Q9Original384b`). Run `lake env bash /path/to/this/package/replay.sh`. The twenty-eight numeric shape checks are sequential by default; the biggest shape files can take substantially longer than the bridges.

[Complete pinned Lean sources](proof-sources.tar.gz). Extract the archive and use its replay script.
