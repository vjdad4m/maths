# Graffiti.pc #199: all loss splits in the separated four-block layout

Lean proves Hamiltonian traceability at orders 15 and 16 for the specific
separated four-block layout, under vertex connectivity three, induced-tree
number at most five, and the additional hypothesis that there is no
independent set of six vertices. The theorem
`Catalogue.traceable_at_fifteen_or_sixteen_of_separated_four_blocks` is in
`src/OneAndThree.lean`.

In the order-15 layout, nontraceability forces a loss split of 4+1 or
1+4. The four lost highs then lie in the singleton high sets, allowing
the earlier tree-budget splice. At order 16, the remaining 3+1, 1+3
and 2+2 splits have their own traceability arguments.

This does not derive the separated four-block layout or the
no-independent-six hypothesis for general minimum counterexamples.
Graffiti.pc #199 remains open.

Use Lean 4.19.0 with Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
on `LEAN_PATH`, then run
`bash graffiti-199-separated-four-blocks/replay.sh` from the repository root.
