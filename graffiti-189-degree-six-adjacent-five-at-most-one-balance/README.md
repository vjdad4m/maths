# Graffiti.pc #189: adjacent order-16 singleton, five visible with at most one balanced dark vertex

In the degree-six order-sixteen inference, an adjacent two-separator
can leave a singleton and a thirteen-vertex shore. If the large shore
has exactly five visible vertices (neighbors of one or both terminals)
and at most one dark vertex at distance two from both terminals,
then the graph has a spanning path. A dark vertex at depth three
is allowed; there is at most one, and it has all its graph neighbors
in the dark block.

There are three common ports and one exclusive of each color.
There are at least six strict depth-two vertices, all of dark degree
at least five. A depth-three vertex also has high dark degree.
If there is no balanced vertex, the entire dark block is
Hamilton-connected by terminal Ore; the common ports are a clique
and reach both exclusives. If there is one balanced vertex, a common
port cannot see both exclusives (it would see all six or more strict
vertices plus the singleton at distance two). High degree forces
the three common ports to form a clique and touch the balance. The
balance must have a dark neighbor (there are only five ports), so
route the dark block without the balance and append it as a bridge
to the common clique. The original graph is reindexed explicitly
and the checked spanning walk transported back.

Main declaration:
Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_of_adjacent_singleton_thirteen_five_at_most_one_balance.

Replay with Lean/Mathlib 4.19.0 and the prior checked adjacent unique/profile,
singleton, cut and Ore modules on LEAN_PATH. All audit lines use only
standard axioms. The residual five-visible cases with two or three
balanced depth-two vertices remain outside this result.
