# Graffiti.pc #189: three-fifths connectivity range

Let d be a degree threshold in a finite connected simple graph. Suppose
each vertex has at most d+1 even-distance vertices (including itself),
and any two distinct vertices include one whose degree is at least d.
If deleting any set of fewer than k vertices preserves connectivity,
then the graph has a spanning path whenever **k ≥ 2000 and 5k ≥ 3d**.
This widens the verified asymptotic connectivity ratio from 2/3 to
3/5; it does not resolve the unrestricted conjecture.

The proof uses a minimum-edge longest path, its omitted root-star, and
a disjoint routing of k hooks from the shore to that path. If removing
the root leaves a 2-connected graph, the one-low Pósa circumference
theorem supplies long terminal routes. Otherwise, the shore minus at
most two cut vertices splits. A private-gate charge bounds shell three,
with different bounds depending on whether the smaller shore contains
a high-degree donor. Independently, first hook ports that contact both
shores can retarget their roots to maximize the cross-shore paths used
in the spacing inequalities. The exact arithmetic combines the
shell bound with ordinary and flexible hook spacing.

`ThreeFifthsDeficit189.lean` contains the final theorems.
Replay with Lean 4.19 and the listed dependencies on LEAN_PATH.

Predecessors: [the two-thirds connectivity package](../graffiti-189-two-thirds-connectivity/), [quadratic connectivity package](../graffiti-189-quadratic-connectivity/), and [the disjoint-hook library](../graffiti-189-shell-three-quadratic/). The source bundle's `DEPENDENCIES.txt` records the exact verified objects. See the [final theorem](ThreeFifthsDeficit189.lean) and [strict replay log](VERIFIED.log).

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
