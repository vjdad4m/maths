# Graffiti.pc #189: degree six, connectivity at least four, order at most 22

Under the original even-distance cap at second-degree threshold six,
a connected graph with vertex connectivity at least four and order
at most 22 has a spanning simple path. Any counterexample of order at
most 23 must have order 23, with a normalized longest path of length 17
and a five-vertex active omitted component.

The proof reuses the normalization and endpoint mark count from the
order-twenty result. At six through eight omitted vertices, pure
Mathlib LRAT proof terms certify that every pair of distinct terminals
has an internal path with at least five vertices. This leaves
distance at least six between pins with different porters. When the
spine has length at most 16, all pins come in two exclusive pairs.
Every high vertex not owning a pair needs inside degree at least six.
For a component with at most six vertices this is impossible; seven
and eight vertices admit denser owner-to-owner routes that exceed
the remaining spine spacing budget.

Main: `Graffiti189LongestPath.SixFourFrontier.traceable_order_twenty_two`
and `Graffiti189LongestPath.SixFourFrontier.frontier_normal_form`.
Strict Lean 4.19.0 with standard axioms only. Sources and trimmed LRAT
certificates are self-contained apart from the pinned prior #189 modules
and Mathlib. The solver is not needed for verification.
