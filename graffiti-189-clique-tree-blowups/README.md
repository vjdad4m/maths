# Graffiti.pc #189 for clique blow-ups of trees

Let G be a finite connected simple graph obtained by replacing every
node of a tree with a nonempty clique and every tree edge with a complete
join between its two cliques. Let d≥5 be the second-smallest degree, or
any threshold with at most one degree below d. If each vertex has at
most d other vertices at even distance, then G has a spanning simple
path. This covers arbitrary order and connectivity in this graph class;
it does not resolve unrestricted #189.

In the quotient, a node with bag size w has degree at most w+1.
Call it tight when the degree equals w+1. After handling original-graph
articulations, each internal bag has size≥2, and the only possible low
degree is in a singleton leaf bag. Sum the degree demands of the
neighbors of a quotient node using disjoint two-step successor groups.
The original parity cap bounds the total weight on each quotient color
side minus the own bag, and yields at most two tight nodes. A size-two
tight node with no low neighbor can occur only at d=6, in which case it
is the unique tight node.

A tree spine passes through the tight nodes in its interior. A generic
walk extension covers all other nodes while saving one visit at every
internal spine node. Its visit multiplicities fit the clique capacities.
The final inflation assigns distinct actual bag vertices to visits and
uses every remaining clique vertex consecutively.

Main theorem:
`Graffiti189LongestPath.TreeBagTraceability.traceable_of_clique_tree_blowup_of_degree_ge_five`.
The graph model is an onto quotient vertex map with the exact indicated
adjacency relation; the proof does not assume any numerical conditions
on its bags beyond those derived in Lean from the original hypothesis.

See the [final Lean module](TreeBagTraceabilityAll189.lean), [strict verification log](VERIFIED.log), and archived dependency list.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
