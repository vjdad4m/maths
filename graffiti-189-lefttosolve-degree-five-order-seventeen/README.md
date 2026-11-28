# Graffiti.pc #189: LeftToSolve degree-five order-seventeen reduction

This is a Lean-checked case split for [one LeftToSolve step](https://lefttosolve.com/p/WrittenOnTheWallII.GraphConjecture189.conjecture189.R2.H2.R1.H1.R1.H2), not a standalone proof of that step or of the full conjecture. The upstream hypotheses force exactly 17 vertices, an even-distance cap of six and at most one vertex of degree below five. The reduction then splits into no separating pair, a nonadjacent separating pair, and an adjacent separating pair.

The split follows the existing [degree-five proof](../graffiti-189-degree-five-complete/) and the [order-seventeen theorem](../graffiti-189-degree-five-order-sixteen/). The three branches have existing mathematical proofs in that collection; this file does not port those proofs to the LeftToSolve checker. On Lean 4.33.1, a local replay using the exact reduction chain and pinned graph definitions (with a narrowed upstream utility import) checked the reduction with only `propext`, `Classical.choice`, and `Quot.sound`. LeftToSolve static lint also passed.

Not submitted upstream: [PR #31988](https://github.com/lefttosolve2/open-math-agents/pull/31988) already addressed the exact target and its official check passed.
