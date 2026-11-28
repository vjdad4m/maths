# Graffiti.pc #189: five-visible residual requires a degree-one/two balance

For the original degree-six, order-16 adjacent singleton+13 case,
five visible vertices yield a spanning path unless there are three
balanced dark vertices, at least two balances have induced dark
degree at most three, and some dark vertex has degree at most two.

When all dark degrees are at least three, start an Ore sequence at a
low prescribed terminal. First complete the five-vertex high core
with that terminal, then boost a backup balance if necessary via
their missing edge. The high core and backup then form a clique.
The core degrees are at least six, so every remaining core edge can
be closed with another vertex of degree at least three. If all
balances are low, bipartite double counting rules out a clique of
balances and supplies the required missing edge. The completed
path is lifted to the original graph.

Main:
Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_of_adjacent_singleton_thirteen_five_unless_small_balances.

Replay Lean/Mathlib 4.19 with preceding q=3 one-low, q=3 dense,
q=2, profile, port and Ore packages on LEAN_PATH. Standard axioms only.
