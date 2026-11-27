# Graffiti.pc #199: connectivity-one and connectivity-two cases

**Partial result.** For a connected graph with vertex connectivity one or two, Lean proves that if the largest induced tree has at most two more vertices than the connectivity, the graph has a Hamiltonian path. This is the full conjectured implication at those two connectivities.

The same source proves structural reductions at connectivity three; it does not prove the conjecture there or at higher connectivity.

See [Proof199K13.lean](src/Proof199K13.lean), theorems `conjecture199_connectivity_one` and `conjecture199_connectivity_two`. In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-199-low-connectivity/replay.sh`.
