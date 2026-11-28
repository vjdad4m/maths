# Graffiti.pc #384b: structural reductions at diversity eleven

This package does not settle diversity eleven. It reduces a possible counterexample
to a spanning triangle-supported graph with exactly the same vertex triangle
counts. Its nonleaves number 10–15. Either all ten nonleaves have degree at least
three, or there are exactly nine high vertices, with distinct counts at least
two, and all other nonleaves are triangular degree-two ears.

A supported pin block with at least two low vertices on one shore excludes a
counterexample. The graph of ears with high anchors therefore cannot contain a
cycle, including duplicate pages with the same two anchors. The general pinned
cut inequality is valid for arbitrary diversity and arbitrary finite simple
graphs.

Entry points: `triangle_supported_reduction`, `ten_to_fifteen`,
`split_profile`, `exact_of_low_pin_block`, `pinned_budget` and `exact_of_book`,
all in the namespace `Graffiti384b.DiversityEleven`. No graph enumeration
enters these proofs.

## Replay

Use Lean 4.19.0 (6caaee842e94) and Mathlib v4.19.0
(c44e0c8ee63ca166450922a373c7409c5d26b00b). Build the complete
[even-palette package](../graffiti-384b-even-palette/) including its pinned
`prior/` closure with its documented cold replay. Keep that build's single
24-module object directory and the Mathlib package objects on `LEAN_PATH`.
Run `lake env bash /path/to/this/package/replay.sh`. The supplied strict
transcript uses the complete cold dependency objects, not stubs. Only
`propext`, `Classical.choice`, and `Quot.sound` enter the audited theorems.
