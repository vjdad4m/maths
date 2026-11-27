# Graffiti.pc #189 at order fifteen and 4+5 attachments

Under the degree-five conjecture's even-distance and degree hypotheses, and connectivity after any single deletion, a distance-two cut pair with two components admitting common neighbors and exactly four and five attachments, respectively, has a Hamiltonian path at order fifteen. This solves the maximum-order case of that profile. Smaller orders and the full conjecture remain open. [Lean statement](src/DegreeFiveBothFourFiveFifteenClose189.lean)

The four-attachment side provides a two-terminal path; the other provides both choices of a rooted path. Closure stays inside the auxiliary shore graph and returns genuine original edges. [Contact constraints](src/DegreeFiveBothFourFiveFifteen189.lean) · [Closure with one exceptional pair](src/RootedOreExceptPair189.lean)

Build the [order-bound](../graffiti-189-both-common-order-bounds/), [exclusive-shore](../graffiti-189-one-exclusive-shore/), [5+5](../graffiti-189-both-five-shores/) and [degree-four](../graffiti-189-complete-degree-four/) dependencies under Lean 4.19.0 and Mathlib 4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Check `sha256sum -c sources.sha256` and compile in `modules.txt` order with asynchronous elaboration disabled and warnings as errors. All seven sources passed strict replay with only the three standard axioms in the printed reports.
