# Graffiti.pc #189: arbitrary-cap two-cut bounds and degree-six reduction

Let G be a finite connected simple graph which stays connected on deleting
any one vertex. Suppose deleting the distinct vertices a,b gives at least
two components. If every vertex has at most d+1 vertices at even distance
(counting itself), then G has at most 6d+2 vertices; if a,b are adjacent,
G has at most 4d+2. In particular, with even-distance caps of seven,
the upper bounds are 38 and 26, respectively.

If in addition at most one vertex has degree below six, then the two
separator vertices have distance at most three. Moreover, if at least
three components occur, some component has no degree-six-or-higher
neighbor of a, and some component has no such neighbor of b. The two
components are allowed to coincide in this declaration. The lower-order
and multi-component exclusions are separate from this package.

## Main Lean declarations

- `Graffiti189LongestPath.CrossSaturation.TwoCutOrder.order_le_six_mul_add_two`
- `Graffiti189LongestPath.CrossSaturation.TwoCutOrder.order_le_four_mul_add_two_of_adjacent`
- `Graffiti189LongestPath.CrossSaturation.TwoCutOrder.order_le_thirty_eight_at_six`
- `Graffiti189LongestPath.CrossSaturation.ThresholdSix.separating_pair_distance_le_three_at_six`
- `Graffiti189LongestPath.CrossSaturation.ThresholdSix.exists_shore_without_high_ports_at_six`

The order bounds cover every vertex off the cut by positive-even
sets from a,b and up to four selected ports. The far-distance argument
uses distance-two and distance-four budgets and does not assume exactly
two components at the outset.

## Replay

Use Lean 4.19.0 and Mathlib 4.19.0, with checked predecessor objects on
LEAN_PATH, including `AdjacentCutFiveActual189`,
`AdjacentCutFiveTwoOrderTwenty189`, `AdjacentCutFiveMixedNineGeom189`,
`OddPortsCut189`, and `DegreeFiveFarCut189`. Run `replay.sh` to check hashes
and build the three modules in order with warnings treated as errors.
The declarations above audit to propext, Classical.choice and Quot.sound
only. This does not prove the whole conjecture or the degree-six case.
