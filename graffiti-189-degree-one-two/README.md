# Graffiti.pc #189 at actual second degree one or two

This is an unrestricted-order Lean proof at actual second-smallest
degree d∈{1,2}. The formal statement only needs at most one vertex with
degree below d and some vertex of degree at most d, both automatic when
d is the actual second degree. Under the original even-distance cap,
the graph has a spanning simple path.

For threshold one, a degree-at-most-one root has radius at most three,
and each of its distance-two and distance-three layers has at most
one vertex. Thus its graph has order at most four. For threshold two,
after the already verified articulation case, a degree-at-most-two
root has radius at most three. If its third layer had at least three
vertices, its second layer would contain exactly two vertices and the
first–second layer interface would have to be a perfect matching:
a first-layer vertex adjacent to both second-layer vertices
would already charge all third-layer vertices. In the matching case
each first-layer vertex spends at least one distance-two slot elsewhere;
the two slots that remain cannot account for three third-layer vertices.
Hence the graph has at most seven vertices. The two small-order
results of [Easwar and Johari, Theorem B](https://arxiv.org/html/2609.11719v1)
then apply, using their prior Lean formalizations. The work here is the
low-degree order reduction and exact dispatcher, not a claim of
priority for the resulting low-degree cases or a general resolution.

Main theorem: `Graffiti189LongestPath.LowDegreeOrders.traceable_of_actual_low_degree`.
The two files replay with Lean 4.19.0 (`-j1 -DElab.async=false
-DwarningAsError=true`) and the pinned earlier #189 modules on LEAN_PATH.
Only `propext`, `Classical.choice`, and `Quot.sound` are used.
