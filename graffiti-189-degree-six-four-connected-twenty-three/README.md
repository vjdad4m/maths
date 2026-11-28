# Graffiti.pc #189: order 23 at second-degree threshold six

A finite connected simple graph of order at most 23 has a spanning path if
deleting fewer than four vertices preserves connectivity, every pair of
distinct vertices includes one of degree at least six, and every vertex
has at most seven vertices at even distance (including itself). Thus
the bound covers the exact degree-six, connectivity-at-least-four case
through order 23. It does not resolve larger graphs or lower connectivity.

The longest-path reduction leaves an 18-vertex spine and a five-vertex
omitted component for the new frontier. The component is complete. Its
four pin positions have exactly one gap of length three owned exclusively
by one vertex; the two other gaps both have length six. The two boundary
placements force the corresponding high-degree endpoint to have at most
five neighbors. In the middle placement the distance-two budget confines
neighbors of the flanking vertices to eight spine positions. A short
case split yields an explicit 19-vertex simple path, a contradiction.

Main: `Graffiti189LongestPath.SixFourOrderTwentyThree.traceable_order_twenty_three`.

Replay with Lean 4.19 and the pinned build dependencies. The order-22
subproof reuses the self-contained marked-wing modules and trimmed LRAT
certificates. The order-23 frontier itself uses only graph-theoretic
proofs and small kernel-evaluated concrete lists; no SAT solver is needed.
