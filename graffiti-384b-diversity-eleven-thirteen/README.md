# Graffiti.pc #384b: the 13-nonisolated lower profile at diversity eleven

For finite simple graphs with thirteen nonisolated vertices, nine
vertices of degree at least three, eleven distinct triangle-count
types, and every edge lying in a triangle, the conjectured
2-domination bound holds. Hence any diversity-eleven counterexample
has a score-preserving supported spanning subgraph that is a
counterexample with nine high vertices and 10–12 nonisolated vertices.
No connectivity assumption is needed.

The pendant case uses three independent low omissions touching at most
five highs. Among at least four remaining untouched highs, choose
three of degree at least four if possible. Otherwise the two cubics
have distinct scores two and three and cannot be adjacent; those two
and one degree-four-or-higher vertex can be omitted together.

In the independent-low case there are four ordinary ears. A footprint
of at most seven high vertices permits the earlier untouched extension.
Otherwise the four ear anchor pairs are disjoint. Among the six choices
of two pairs to swap, each failed swap has an obstructing anchor of
triangle score at most four. It obstructs at most one choice, and
the distinct high scores are at least two, so there are at most three
such anchors. This is an analytic counting proof, not graph enumeration.

Main declarations are `Graffiti384b.DiversityEleven.exact_thirteen_lower`
and `Graffiti384b.DiversityEleven.residual_eleven_at_most_twelve`.
The full diversity-eleven and general #384b conjectures remain open.

## Replay

Lean 4.19.0 (6caaee842e94), Mathlib v4.19.0
(c44e0c8ee63ca166450922a373c7409c5d26b00b). Put the preceding
diversity-eleven-structure, lower, upper, and large-lower object
directories and their transitive prerequisites on LEAN_PATH. Then run
`lake env bash /path/to/this/package/replay.sh`. Axioms audited:
`propext`, `Classical.choice`, and `Quot.sound`.
