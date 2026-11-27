# Graffiti.pc #189: the three-omission order-15 case

For the 2-connected degree-four case, Lean proves traceability whenever
an edge-optimal longest path has eleven edges, exactly three omitted vertices,
and both endpoints of degree at least four. Edge-optimal means maximizing
the edge count among omitted vertices among longest paths.

The proof constrains the common attachments of the omitted vertices,
uses an endpoint distance-two bound to force additional edges, and splices
all three omitted vertices into one of seven explicit Hamiltonian paths.
Lean checks the splices without enumerating graphs.
The exact result is `traceable_if_three_off_order_fifteen`.
The full degree-four order-15 case and general conjecture remain open here.

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
on `LEAN_PATH`. Run `bash graffiti-189-order-fifteen-three-off/replay.sh`
from the repository root.
