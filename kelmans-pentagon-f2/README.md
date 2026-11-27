# Kelmans: a conditional pentagon case under cyclic T2

**Partial result.** Take a finite simple cubic graph of order (4 pmod{6}) with the exact four-edge and five-edge cut conditions in the theorem, no four-cycles, and a pentagon numbered 0 through 4. If the exterior contacts at corners 1 and 4 are nonadjacent, then cyclic T2 implies that deleting corner 0 leaves a (P_3)-factor using none of the three other exterior wires.

The proof completes the exterior to a cubic graph by using a three-vertex path with the five ports assigned in a specified order. A nontrivial small cut of that completion would separate one paired set of ports from the other three. Under the five-edge cut condition, that pair would have to belong to two adjacent exterior contacts. The geometric hypotheses exclude this in the prescribed routing; T2 then deletes the appropriate adjacent pair in the cap. The remaining cap vertex's tile can be transferred back to the pentagon.

The three-vertex cap topology is from the five-edge-shore completion studied by [Máčajová and Rajník](https://arxiv.org/abs/2107.09756), notably Definition 5, Lemma 6 and Theorem 9. This proof concerns the fixed pairing for the factor transfer, not priority for the cap itself. The adjacent-contact case is not covered.

See [the exact theorem](src/PentagonArbitrary.lean), and run `lake env bash /path/to/maths/kelmans-pentagon-f2/replay.sh` in Lean and Mathlib 4.19.0. Neither general F2 nor the general Kelmans conjecture is resolved.
