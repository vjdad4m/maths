# Graffiti.pc #189: quadratic connectivity range

Let d be the degree threshold and suppose a finite connected simple graph
has at most d+1 even-distance vertices (including itself) at each vertex,
and each distinct pair has one vertex of degree at least d. If deletion
of fewer than k vertices preserves connectivity, then the graph is
traceable whenever **(d+1)^2+8(d−k) < 2k(k+1)**, with natural truncation
for d−k. This covers asymptotically k/d greater than 1/sqrt(2), and the
whole k=d−3 regime for every d≥14. It does not settle lower connectivity.

The proof first eliminates all gap-two neighbors on an edge-minimal
longest path when k exceeds twice the pin ceiling. This couples the
boundary deficit to the pin count. It then finds internal paths between
prescribed terminals by greedy extension, with no assumption that the
root-deleted shore is two-connected. The five radial shells, the standalone
shell-three quadratic, and weighted hook spacing imply a contradiction.

The checked amalgamation is QuadraticDeficitAll189.lean. Replay with
Lean/Mathlib 4.19 and the earlier #189 interfaces, including
WideRatioDeficitAll189 and StandaloneShellQuadratic189, on LEAN_PATH.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
