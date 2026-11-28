# Graffiti.pc #189: the 7+11 split at a degree-six distance-three cut

Lean rules out the 7+11 configuration at an actual two-shore separator
whose terminals are at distance at least three. The proof counts exactly
which of eight terminal-visibility roles can be adjacent within each
shore or supply a positive even distance, using the threshold-six
degree assumption and the absence of bridges/articulation vertices.

The dispatcher proves that, through order 20, all graphs in this branch
are traceable unless the separator splits them into shores of 6 and
12 and each nonport in the 12-shore lies at distance exactly two from
at least one cut terminal. This last case is not closed here.

Main theorems in Graffiti189LongestPath.CrossSaturation.ThresholdSix:
- no_seven_eleven_shores
- traceable_or_six_twelve_at_six_distance_three_order_twenty

Only propext, Classical.choice and Quot.sound are used. The linear
subproof consists of ordinary Lean omega proofs; no solver output is
trusted at runtime.
