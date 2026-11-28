# Graffiti.pc #189: both endpoints of a distance-three cut have degree at least five

Under the degree-five #189 hypotheses, let a and b be at distance at
least three and let their deletion leave two components. Neither a
nor b can be the unique vertex of degree below five. The theorem applies
to the original graph even when the two degrees differ.

If a cut endpoint c were low, each of its neighbors on each shore
would be high. A high neighbor has at least five neighbors total,
cannot meet the other cut endpoint, and has at most the cut endpoint
and the other same-color neighbors available outside the second shell
of c. Summed over the two shores, this forces at least six vertices
at distance two from c, exceeding its allowance of five.

[Exact Lean theorem](DistanceThreeBothHigh189.lean) · [Strict replay report](Strict.log) · [Checked baseline](../graffiti-189-degree-five-cuts/)

Build the baseline in Lean/Mathlib v4.19.0, then run
`lean -DwarningAsError=true DistanceThreeBothHigh189.lean` with its
objects on LEAN_PATH. This is a structural reduction, not a
traceability theorem for all distance-three cuts.
