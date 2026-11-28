# Graffiti.pc #133: Left to Solve path-six H2 step

One [reduction step](https://lefttosolve.com/p/WrittenOnTheWallII.GraphConjecture133.conjecture133.R1.H1.R1.H2.R1.H1.R1.H2), not the full conjecture. This reuses the induced-seven proof in [merged Left to Solve PR #13854](https://github.com/lefttosolve2/open-math-agents/pull/13854). A connected graph with no ordinary 4-cycle and with average local independence strictly greater than 3 has an induced path on at least seven vertices. Thus a six-vertex maximum implies that the average is at most 3; the two extra structural hypotheses in H2 are not needed.

The previous proof body is unchanged. The submission switches the reduction import and target, and introduces the two additional hypotheses without using them. The exact file is for the upstream Lean checker.

SHA-256: `b2c16ba2073b9265907f3283144893e114dfc50d1baebeb4f76e6681b63e2517`.
