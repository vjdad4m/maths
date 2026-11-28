# Graffiti.pc #189: two-thirds connectivity range

Let d be a degree threshold in a finite connected simple graph. Assume
that each vertex has at most d+1 even-distance vertices, including itself,
and that any two distinct vertices include one of degree at least d.
If deletion of fewer than k vertices preserves connectivity, then the
graph is traceable whenever **3k ≥ 2d+8**. This covers asymptotically
two-thirds connectivity relative to the degree threshold, not all
connectivities.

On a longest minimum-edge path, the root-deleted omitted shore either
has the connectivity needed for long Pósa routes or splits after a
small deletion. In the split case, the universal first-shell donor
cover charges not only other donors, but also all opposite-shore
vertices outside the donor cover. There is at most one spare cut donor.
The resulting strengthened third-shell estimate contradicts the greedy
terminal-path and weighted hook-spacing lower bound.

TwoThirdsDeficitAll189.lean is the checked amalgamation. Replay with
Lean/Mathlib 4.19 and the earlier #189 interfaces including
QuadraticDeficitAll189 on LEAN_PATH.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
