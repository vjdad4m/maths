# Graffiti.pc #189: adjacent order-16 singleton profiles and unique ports

Under the degree-six and even-distance-cap-seven hypotheses, an adjacent
two-vertex cut leaving one singleton and a shore of order 13 has exactly
five or six visible vertices in the larger shore. With five visible
vertices there is precisely one exclusive port per terminal and every
large-shore vertex has nearest-terminal distance at most three. With six,
each terminal has one or two exclusive ports, and the dark vertices are
all at nearest-terminal distance two.

When there are six visible vertices and exactly one exclusive port on
each side, every case is traceable. The checked normalized routes for at
most two balanced vertices also apply here without any terminal adjacency
assumption. For three balanced vertices the same even-distance saturation
argument forces minimum degree two in the common-port block: a low common
port would see all four strict vertices and the singleton at distance two,
so among its two common nonneighbors some other common port shares no
neighbor with it, contradicting their combined degree. Cross-edge Ore
closure routes the dark block when all balances have enough dark degree.
Otherwise a low balance can be placed at the end, beside the common
block. If another balance is low after its deletion, the two strict
neighborhoods are complementary and the one-exception Ore path rule
inserts the remaining low point.

Main checked declarations:
- Graffiti189LongestPath.CrossSaturation.ThresholdSix.adjacent_singleton_thirteen_visible_profile
- Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_of_adjacent_singleton_thirteen_unique

Replay on Lean and Mathlib 4.19.0, with the checked earlier singleton, dark,
cut and terminal Ore modules on LEAN_PATH. Only standard axioms occur.
The five-visible and multiple-exclusive six-visible cases remain open
in this package; the full degree-six conjecture is not claimed.
