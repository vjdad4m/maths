# Graffiti.pc #133: LeftToSolve radius-four/path-seven step

This is the Lean 4.33.1 port of the [existing induced-eight-or-small-radius theorem](../graffiti-133-full-four/src/FinalEight133.lean) to [LeftToSolve's radius-four/path-seven reduction step](https://lefttosolve.com/p/WrittenOnTheWallII.GraphConjecture133.conjecture133.R1.H1.R1.H2.R1.H2). It is not a resolution of the full conjecture.

For an ordinary-C4-free connected graph whose average local independence is at least three, the original theorem produces an induced path on eight vertices or a center of radius at most three. The port proves that both witnesses contradict the exact upstream hypotheses. The two extra hypotheses of that step are not needed.

Local replay on Lean 4.33.1 used the exact upstream reduction chain and pinned graph invariants, with a narrowed Formal Conjectures utility import. The check reported only `propext`, `Classical.choice`, and `Quot.sound`. Upstream static lint passed.
