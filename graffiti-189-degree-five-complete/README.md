# Graffiti.pc #189: the complete degree-five threshold

**Every finite connected simple graph with at most one vertex of degree below
five, and at most six even-distance vertices from each vertex including
itself, has a spanning path.** In particular this proves the conjecture
when the second-smallest degree is five. This is not a resolution for all
higher degrees.

The [earlier reduction](../graffiti-189-degree-five-only-fourteen/) restricts
any counterexample at this threshold to precisely fourteen vertices. It uses
the independently [formalized small-order theorem of Rohun Easwar and Shaurya
Johari](../graffiti-189-easwar-johari-order-two-d-plus-three/) and our
order bounds. The final proof handles the remaining adjacency profiles
for a two-vertex cut isolating a singleton. See the
[written discussion](ORDER-FOURTEEN-CASES.md) for the case construction.
Lean checks the graph-specific hypotheses of each finite certificate and
the transfer between the original graph and its fourteen-vertex labeling.
The LRAT certificates produce Lean proof terms; no native evaluator or
external solver axiom is used.

Final declaration:
[`Graffiti189LongestPath.traceable_at_degree_five`](DegreeFiveComplete189.lean).
The [strict audit](VERIFIED.log) records the successful serial stages;
the only axioms reported are `propext`, `Classical.choice`, and `Quot.sound`.

## Replay

Use Lean and Mathlib 4.19.0. Build the earlier packages linked above and the
[order-fourteen frontier closures](../graffiti-189-order-fourteen-two-profile-closure/),
[empty-even closures](../graffiti-189-order-fourteen-empty-even/), and
[order-fifteen singleton geometry](../graffiti-189-degree-five-order-fourteen/).
The shared certificate checker and circuit semantics are in
[the #384b three-tag archive](../graffiti-384b-diversity-eleven-three-tag/).
Supply compiled `Mathlib.Tactic.Sat.FromLRAT` in the same Mathlib overlay as
the earlier graph libraries, and use the earlier `ArticulationClique189`
compatibility object if needed. Extract this archive, set LEAN_PATH for
those objects, and run `bash replay.sh` from the archive directory. The
two source and certificate paths in the RUP modules are relative to that
directory.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
