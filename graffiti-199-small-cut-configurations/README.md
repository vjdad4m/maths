# Graffiti.pc #199: Hamiltonian paths in small-cut configurations

**Partial result.** Lean constructs Hamiltonian paths for the labelled order-15 and order-16 two-singleton configurations with loss splits (1,4) and (0,4), under the exact adjacency, small-cut, and degree hypotheses in [FootprintApplication.lean](src/FootprintApplication.lean). The construction uses the finite path table in DepletedPaths and proves that a crossing edge suitable for the splice exists.

Lean also verifies the three-singleton construction when the two shared triangle tips lie in opposite halves of the paired block ([SplitTipsSplice.lean](src/SplitTipsSplice.lean)). When the tips lie in the same half, the available-end and singleton-contact lemmas are checked ([SameHalfAccess.lean](src/SameHalfAccess.lean)), but the full splice is not established by this package.

These are standalone statements about explicit configurations. This package does **not** prove that an arbitrary minimum counterexample to #199 must fit these labelled hypotheses, and it does not prove the full conjecture.

In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-199-small-cut-configurations/replay.sh`. The replay regenerates the finite table and checks the entire source proof.
