# Graffiti.pc #189: at least eighty percent connectivity

If a finite connected simple graph has at most d+1 even-distance
vertices at each vertex (including itself), every pair of distinct
vertices includes one of degree at least d, and deletion of fewer than
k vertices preserves connectivity, then it is traceable whenever
**5k ≥ 4d+6**. In particular, the entire regime κ≥d−3 is proved for
d≥21, and the allowed connectivity deficit grows linearly with d.
Smaller connectivity is not covered by this result.

The improvement uses a minimum family of donors for the cut gateways.
Every donor has a private gateway. For any fixed donor, each other
donor consumes a distinct distance-two slot: its private gateway if it
is adjacent, or the donor itself through the universal shore root if it
is not. This gives a quadratic bound on the third-shell order independent
of the shore height. The earlier defective Hall and one-low-degree
circumference bounds supply terminal routes; weighted hook spacing
then contradicts that quadratic bound.

`WideRatioDeficitAll189.lean` is the checked amalgamation of the files
under `modules/`. Replay with Lean/Mathlib 4.19 and prior #189 theorem
objects (including `ScaledDeficitAll189`) on LEAN_PATH.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
