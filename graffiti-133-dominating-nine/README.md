# Graffiti.pc #133: the dominating nine-cycle branch

**Partial result.** In a finite graph with no ordinary four-cycle and a dominating induced nine-cycle, average local independence strictly above four forces an induced path on nine vertices. Thus Lean proves the mean-five, radius-four case with such a dominating cycle. The floored version follows at radius at most four and floored mean at most five under the same cycle and four-cycle hypotheses.

The proof reduces the contacts with the cycle to 57 possible nonempty masks. It checks the pair constraints for two outside vertices and uses a 43-node coloring-and-branching certificate on the resulting score graph. The bound on the score gives a bound on the sum of degrees, hence on the sum of local independence numbers. Python generates the witness table; Lean checks the finite exclusions, score certificate and transfer to arbitrary finite graphs.

Without an induced nine-vertex path, a connected four-cycle-free graph of mean above four must instead have a connected dominating induced-(P_7)-free subgraph. This leaves an open case, as do the other residual radii in the exact mean-five range. See [the main theorem](src/C9Main133.lean) and [the exact residual cases](src/ResidualRealFive133.lean).

In Lean and Mathlib 4.19.0, run `lake env bash /path/to/maths/graffiti-133-dominating-nine/replay.sh`. The verifier rebuilds the published prerequisite modules and all seven new modules.
