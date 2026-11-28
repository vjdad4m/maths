# Graffiti.pc #189, degree six: every actual three-cut has exactly two shores

Let G be a finite connected simple graph with at most one vertex of degree
below six and with at most seven even-distance vertices (counting the root)
from each vertex. Assume deleting fewer than three vertices preserves
connectivity. Then deleting any three-vertex set leaves at most two
components. In particular every actual separating three-set leaves exactly
two. The exact theorem is
`Graffiti189LongestPath.ThresholdSix.ThreeCut.three_cut_at_most_two_components`.
This is a structural reduction, not a proof of a spanning path.

## Proof outline

The earlier singleton theorem allows us to assume three nonsingleton shores,
each of size at least four. One shore has a universal port, and two different
shores cannot both have universal ports. The two foreign shores therefore
have exactly three visible vertices, each of rank at most two. If all
terminals have a high port in both foreign shores, summing their
distance-two charges gives an immediate contradiction.

The alternative is a terminal whose sole port on one foreign shore is the
unique low vertex. A two-terminal Hall bound prevents another such terminal
on that shore. The low vertex spends at least one local distance-two slot.
Charge summation leaves at most three missing incidences at the universal
shore. The exceptional terminal has a rank-two port in the other foreign
shore; rank one alone would overspend its distance-two cap. The rank-two
port sees two vertices on the low shore and enough vertices on the universal
shore to overspend, unless the universal shore has order four. In order four,
exact saturation forces internal universality around this port, and then
its second terminal exposes one further foreign vertex, a contradiction.

## Replay

Use Lean/Mathlib v4.19.0. Set LEAN_PATH to the object closure of
[the singleton and two-universal three-cut package](../graffiti-189-degree-six-three-cut-singletons/).
Compile the six modules shown in StrictReplay.log in order, with
`-j1 -s32768 -DElab.async=false -DwarningAsError=true`.
Only standard axioms; no numerical solver or graph search is used.
