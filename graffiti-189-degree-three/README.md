# Graffiti.pc #189 at actual second-smallest degree three

**Scope**: arbitrary finite connected simple G with actual second-smallest
degree 3. The theorem accepts the weaker sufficient thresholds:
at most one vertex has degree below 3, and some vertex has degree at most
3. If every vertex has at most 3 other even-distance vertices, then G
has a spanning simple path. This is not unrestricted #189.

The Easwar–Johari results cover articulation graphs and order at most 9
[Theorem B](https://arxiv.org/html/2609.11719v1). Their Lean formalizations
are pinned dependencies. For a larger 2-connected graph, start from a
vertex of minimum degree (two or three), and index the successive shells.
The even-distance cap forces radius at most four, and |D₂|+|D₄|≤3.
The shell model is exact: an edge connects only equal or consecutive
distance layers, and every nonroot vertex has a predecessor. The chosen
small-degree root is the only possible vertex of degree below three.

The eleven finite certificates use graph-native clauses:
- each forbidden layer edge is absent;
- every nonroot vertex has a predecessor;
- the applicable vertices have degree at least three;
- a two-step walk between distinct nonadjacent endpoints gives a
  distance-two vertex;
- no four distinct vertices have distance two from any one pivot;
- a proposed Hamilton path must omit an edge if the graph is nontraceable.

Four prefix certificates permit choosing any five distance-three
vertices even when the graph has further vertices, and refute the
resulting constraints. The checked graph lift uses the actual graph
distance, and only tests degree in rows where all neighbors are retained.
With |D₃|≤4, the seven remaining profiles are checked in full. Some
profiles are infeasible; the route candidates for the others are
concrete permutations and Lean proves they would be Hamilton paths
when their adjacency literals all hold.

The search generator supplies DIMACS and ASCII LRAT files. Lean checks
every used proof step through Mathlib's proof-term checker, every
clause's graph semantics, the exact formula correspondence, and the
final dispatcher. The checker is adapted from proof-term code used for
#384b. The solver and generator need not be trusted or rerun for replay.
No native proof axiom is used. This is an independent low-degree
reduction and formalization, not a claim of priority.

Main theorem:
`Graffiti189LongestPath.GraphSat.traceable_at_actual_degree_three`.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
