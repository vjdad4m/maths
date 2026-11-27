# Graffiti.pc #133: Left to Solve radius-three, path-six step

This is the single-file port of the repository's induced-seven proof to Lean 4.33.1 for [the Left to Solve H1 step](https://lefttosolve.com/p/WrittenOnTheWallII.GraphConjecture133.conjecture133.R1.H1.R1.H2.R1.H1). It is not a resolution of the full conjecture.

The proof uses the stronger fact that a connected graph without an ordinary 4-cycle and with average local independence greater than 3 has an induced path on at least seven vertices, contradicting the six-vertex maximum in the target. The original graph proof is in [graffiti-133-induced-seven](../graffiti-133-induced-seven) and the invariant adapter in [graffiti-133-lefttosolve-path-six](../graffiti-133-lefttosolve-path-six).

The entire proof body passed Lean 4.33.1 against the exact pinned target and the relevant upstream definitions in a local fixture. The axiom report is [included](lean-4.33.1-fixture-session-28304.log). This records a fixture replay, not a run of the full upstream import or acceptance by Left to Solve.

Submission-source SHA-256: `7ccb631676b7c74278df8bb66006f88793c9af339dfe5b480f690c70165840cd`.
