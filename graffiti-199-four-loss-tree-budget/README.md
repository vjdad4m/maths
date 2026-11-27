# Graffiti.pc #199: deriving the four-loss crossing from the tree bound

For the published four-block configuration with all four high vertices of
the depleted pair in the singleton high sets, the induced-tree bound and
vertex connectivity three already force the crossing required by the
Hamiltonian splice. The proof no longer assumes the stronger crossing
condition from the earlier order-15/16 certificate.

Six exceptional local configurations lack enough path endpoints. If certain
cross-edges are absent, Lean checks an induced tree of order six, contrary
to the bound of five. The forced edges give paths to every high endpoint.
Three-connectivity then supplies a crossing after deleting at most two
vertices. The finite table enumerates just the exceptional configurations;
its witnesses and paths are checked in Lean.

This is a conditional branch. It does not derive the four-block cover
or membership of the depleted pair in the singleton high sets from an
arbitrary graph. The full conjecture remains open. The main theorem is
`Catalogue.traceable_of_depleted_pair_of_tree_budget` in
`src/FourLossFromCatalogue.lean`.

Use Lean 4.19.0 with Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
and an existing Mathlib `LEAN_PATH`. From the repository root run
`bash graffiti-199-four-loss-tree-budget/replay.sh`.
