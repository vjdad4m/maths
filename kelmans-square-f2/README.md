# Kelmans: deleting a corner of a four-cycle under cyclic T2

**Conditional partial result.** In a cubic graph of order (4 pmod{6}) and at least seven vertices, suppose every cut with at most three edges has a side of size at most one. If cyclic T2 holds, then deleting any corner of any four-cycle leaves a (P_3)-factor that uses **none** of the four exterior edges of that cycle.

Here T2 is the adjacent-pair deletion assertion for cubic 3-connected graphs with this cut condition and order (2 pmod{6}). The proof establishes that a four-cycle is automatically induced and has four distinct exterior contacts under the stated hypotheses. It caps the exterior of the cycle with an adjacent pair, uses T2 on that pair, and adds the remaining three cycle vertices as a path.

The adjacent-pair completion of a four-edge shore is due to Andersen, Fleischner and Jackson, Lemma 7, as discussed in [Goedgebeur, Mácajová and Škoviera, Lemma 3.2 and Theorem 3.3](https://backoffice.biblio.ugent.be/download/8637147/8637151). The certificate formalizes a completion argument and its conditional application here; it makes no priority claim for the completion theorem.

- [Completion geometry](src/SquareCapGeometry.lean)
- [Factor transfer](src/SquareCapFactor.lean)
- [Arbitrary graph, all exterior edges avoided](src/SquareCapArbitrary.lean)

This result is not a proof of unrestricted F2 or the Kelmans conjecture. In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/kelmans-square-f2/replay.sh`.
