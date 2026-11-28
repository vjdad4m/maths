# Graffiti.pc #384b: exactly eleven nonleaves at diversity nine

For any finite simple graph with exactly eleven vertices of degree at
least two and exactly nine distinct triangle-count types, the exact
two-domination bound holds. Connectedness is not required.

Main theorem: `Graffiti384b.EffectiveSearch.Q11.exact_of_nine_types`
in `src/Q11Exact384b.lean`. The finite reduction normalizes the two vertices
having the largest distinct triangle counts, checks a decision tree for
each normalized contact shape, and lifts a retained support witness to
the ambient graph. All numeric branches are checked with ordinary Lean
`decide`; no external solver is run during replay.

Use Lean 4.19.0 (6caaee842e94) and Mathlib v4.19.0
(c44e0c8ee63ca166450922a373c7409c5d26b00b). Build the baseline,
diversity-29, eight-nonleaf, and nine-nonleaf packages, and leave
their objects and Mathlib on LEAN_PATH. Run
`lake env bash /path/to/this/package/replay.sh`.

[Complete pinned Lean sources](proof-sources.tar.gz). Extract the archive and use its replay script.
