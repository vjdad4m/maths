# Graffiti.pc #189: four-sevenths connectivity range

For a finite connected simple graph, assume:
- Every vertex has at most d+1 even-distance vertices, counting itself.
- Any two distinct vertices include one of degree at least d.
- Deleting any set of fewer than k vertices preserves connectivity.

If **k ≥ 10,000 and 7k ≥ 4d + 4,000**, the graph has a spanning path.
This verifies an additional connectivity range, asymptotically 4/7 of the
degree threshold. It does not settle unrestricted #189.

The split-shore analysis combines two complementary counts. An omitted
donor charges each missed path pin directly and the two immediate flanks
of every adjacent pin (at most one shared flank is lost), disjointly from
private gate charges. A high donor's ambient degree in turn forces it
to have enough neighbors outside its shore, even after its missed pins
and other donors' private gates are removed. Counting the ports not
reached by either split side gives an independent shell bound and the
number of flexible hooks. These shell estimates and hook spacing beat
the required total order in each pin range.

Main theorem:
`Graffiti189LongestPath.FourSeventhsDeficit.traceable_of_four_sevenths_connectivity`
in `FourSeventhsCombined189.lean`. The separate sources are provided in
`modules/`. Replay with the pinned Lean/Mathlib and earlier #189 interfaces
on LEAN_PATH.

See the [final declaration](FourSeventhsDeficit189.lean), [strict replay log](VERIFIED.log), and [three-fifths predecessor](../graffiti-189-three-fifths-connectivity/).

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
