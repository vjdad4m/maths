# Graffiti.pc #189: connectivity in a proportional range

A finite connected simple graph is traceable if the upper bound on
even-distance vertices (including the root) is d+1, any distinct pair
includes a vertex of degree at least d, and deletion of fewer than k
vertices preserves connectivity, provided **29k ≥ 28d+20**.
This admits a degree-connectivity gap growing linearly with d. For
example it covers the entire regime κ≥d−3 whenever d≥107. It does not
settle graph classes of lower connectivity.

The proof uses at most d−1 boundary vertices in the normalized omitted
star (from the exact count of path flanks). Hall with arbitrary cut
deficit supplies an induced shore degree floor and two-deletion
connectivity for the root-deleted shore. The already verified
circumference theorem then supplies uniformly long terminal routes.
For the order upper bound there are three possibilities: sparse donors
charge many external gateways to a single budget, a heavily attached
donor can enforce that sparsity, or dense donors reserve many of their
distance-two slots for distinct representative gateways. Arithmetic
contradicts the order lower bound from a disjoint k-hook fan in every case.

`ScaledDeficitAll189.lean` is the exact verified amalgamation. The source
fragments live in `modules/`. The replay requires Lean/Mathlib 4.19 and
the prior #189 theorem objects, including `DeficitThreeAll189`, on LEAN_PATH.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
