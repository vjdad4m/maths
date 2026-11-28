# Graffiti.pc #189: complete five-visible adjacent singleton case

The degree-six order-16 adjacent two-cut with a singleton and
thirteen-vertex shore always has a spanning path if the large shore
has exactly five vertices adjacent to a cut terminal. This theorem
is on the original arbitrary finite simple graph with the usual
degree-six threshold, even-distance cap seven, and deletion
connectivity. There is no hypothesis on the dark degrees or the
numbers of balanced vertices.

The last row has three balances of dark degree at most three and
at least one of degree at most two. Double counting shows a total
internal degree sum of at least eighteen on the five-vertex dark
core, hence terminal Ore there. Every balance has a neighbor
in that core. The remaining eleven vertices are covered by a
tail starting at a balance. A 97-clause, 18-variable LRAT
certificate checked as a Lean proof term proves that at least
one of 49 finite tail templates applies. The template orders and
their edge data are independently kernel-checked and transferred
to the normalized graph before the final path is transported back.

Main:
Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_of_adjacent_singleton_thirteen_five_visible.

Replay with pinned Lean/Mathlib 4.19 and earlier five-visible degree-six
adjacent singleton packages, including the three-balance has-high and
LRAT checker front end, on LEAN_PATH. Only standard axioms; neither
native decision axioms nor proof placeholders. The finite clause and
proof files are included; solver runs are not needed during replay.

This closes the five-visible case only. Six-visible profiles with
a positive balanced count and multiple exclusive ports remain.
