# Graffiti.pc #189: exact adjacent two-cut component count

This package formalizes a reduction in the degree-five threshold case
of Graffiti.pc #189. Let G be a finite connected simple graph such that
deleting any one vertex leaves it connected, each vertex has at most
six even-distance vertices counting itself, and at most one vertex
has degree below five. If a,b are adjacent and form a genuine two-cut,
then deleting a and b leaves **exactly two components**. This does not
prove traceability for the remaining two-component case and does not
settle the entire conjecture.

The exact interface is
`Graffiti189LongestPath.CrossSaturation.FiveAdjacent.component_card_eq_two_at_genuine_adjacent_cut`.
The graph-to-profile reduction uses the nearer endpoint(s) and parity
of distance to {a,b}. With adjacent terminals, cross-shore distances
are the sum of depths, with one extra edge exactly when both uniquely
nearer endpoints differ. This gives exact parity rows and budget
inequalities. Analytic degree constraints eliminate head orders
(4,4), (4,5) and (6,6). For the other cases the third shore's profile
can be decreased to the second shore's order while retaining the
necessary two-port condition. The remaining small integer certificates
are computed by kernel reduction. There is no native reduction oracle,
external solver assumption or unchecked graph enumeration.

Lean 4.19.0, standard axioms only. See `replay.sh` and `SHA256SUMS`.
Use Lean 4.19.0 with [Mathlib v4.19.0](https://github.com/leanprover-community/mathlib4/tree/v4.19.0)
and its built packages on `LEAN_PATH`. The replay builds exactly two
pinned predecessor modules from the surrounding repository (or from
`GRAFF189_PREDECESSOR_REPO`), verifying both source hashes first:
[SmallSeparator189](https://github.com/vjdad4m/maths/blob/625b3818002a9cac2974db54df9686f32ec5c58a/graffiti-189/src/SmallSeparator189.lean)
and
[CrossSaturation189](https://github.com/vjdad4m/maths/blob/625b3818002a9cac2974db54df9686f32ec5c58a/graffiti-189-cross-saturation/src/CrossSaturation189.lean).
The previous partial adjacent-shore result is at
[625b381](https://github.com/vjdad4m/maths/commit/625b3818002a9cac2974db54df9686f32ec5c58a);
the independent nonadjacent-cut theorem is at
[b66ce45](https://github.com/vjdad4m/maths/commit/b66ce451b53e56bf8c2c8ae8476ece4c7e8c96ec)
and is not needed for this proof.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
