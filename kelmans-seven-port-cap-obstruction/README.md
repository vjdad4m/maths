# Kelmans vertex-and-edge deletion: a seven-port cap obstruction

This is a **counterexample to a particular reduction**, not to the
Kelmans conjecture or its strengthened vertex-and-edge-deletion form.
The package checks an explicit 16-vertex cubic, 3-connected graph with
the cyclic-five cut property, no 4-cycle, and five independent contacts
at the theta attachment. Deleting vertex 6 and omitting the exterior
edge `14–15` leaves a graph with the required three-vertex-path factor.

There are eight possible live ears considered by the reduction, with
three possible wire palettes for each. All 24 resulting edge-plus-singleton
caps have a nontrivial 3-edge cut, so none is cyclically four-edge-connected.
`SevenPortObstruction.exhausts_live_ears` and `all_twenty_four_bad` check
the exact scope of that enumeration and exhibit the cuts. The layout
module independently checks the contacts and retained incidences. A separate
The cycle certificate verifies an explicit cycle in each shore of every cut.
`SevenPortTheta.all_thirteen_modes` theorem checks the finite local
tile patterns; it does not assert that the caps exist in general.

Use Lean 4.19.0 with Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
and an existing Mathlib `LEAN_PATH`. Run
`bash kelmans-seven-port-cap-obstruction/replay.sh` from the repository root.
