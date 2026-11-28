# Graffiti.pc #189: five-ninths connectivity range

Assume that a finite connected simple graph has at most d+1 even-distance
vertices from every vertex, counting the vertex itself, and that any
two distinct vertices include one of degree at least d. Assume deleting
any set of fewer than k vertices preserves connectivity. If
**k ≥ 100,000 and 9k ≥ 5d**, then the graph has a spanning path.
This is an additional connectivity range, not unrestricted #189.

The improvement uses the lower bound on **each** split shore's missed
boundary reach, not only on the sum. The resulting lower bounds on
shore sizes add a new quadratic estimate for the third distance layer;
this closes the intermediate pin range where the previous shell
estimates and spacing were too weak.

Main theorem
`Graffiti189LongestPath.FiveNinthsDeficit.traceable_of_five_ninths_connectivity`
is in `FiveNinthsCombined189.lean`. The amalgamation also checks three
auxiliary arithmetic lemmas for possible further range improvements;
those do not by themselves extend this graph theorem. Separate editable
module sources are supplied in `modules/`. Replay with the pinned Lean,
Mathlib and earlier #189 compiled interfaces on LEAN_PATH.

See the [final declaration](FiveNinthsDeficit189.lean), [strict replay log](VERIFIED.log), and [four-sevenths predecessor](../graffiti-189-four-sevenths-connectivity/).

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
