# Graffiti.pc #189: degree five and an adjacent separating pair

This is a partial formalization, not a proof of #189 or of traceability
for all adjacent cuts. If every vertex has at most six even-distance
vertices counting itself, deleting fewer than two vertices leaves the
graph connected, and at most one vertex has degree below five, then an
actual adjacent separating pair satisfies:

- The graph has at most 21 vertices, or 17 if the cut vertices are twins.
- The total order plus the number of exclusive neighbors of either cut
  vertex (not counting the other cut vertex) is at most 22.
- Deleting the cut yields exactly two or three connected components.
- If exactly three components remain, none is a singleton, and there is
  a shore on 5–7 vertices in which every vertex has degree at least five
  in the original graph. No wholly high order-four shore can coexist
  with two shores of order at least four.
  Moreover, three shores are impossible if the cut endpoints are twins.
- Any shore with exactly two visible vertices and an interior yields
  another actual two-cut and a strictly smaller shore. In particular
  if the original shore is minimum among all adjacent two-cuts, the
  new two-cut has nonadjacent endpoints. This reduction does not
  assume that the nonadjacent cases are solved.

Lean 4.19.0 standard axioms only. Run `./replay.sh` with Lean 4.19 on
PATH and compatible Mathlib and `CrossSaturation189` build directories on
LEAN_PATH. The numerical exploratory diagnostics used in development
are not used in the formal results and are not included.
