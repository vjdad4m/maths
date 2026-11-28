# Graffiti.pc #189: formalization of Ádám Vajda's two-cut findings

These general-degree proofs concern two-vertex separators, not all of conjecture #189. They rule out order n > 3d in the specified far-port and mirrored near-port configurations at cut-terminal distance three. The result is an order exclusion in those configurations, not a proof of traceability for every surviving graph.

- `SixCentreGraph189.lean`: exact cross-cut distance, coverage table applied to graphs, and `six_centre_bound` in the equivalent additive form 2n+g ≤ 6d+f. The corollaries give n ≤ 3d when f ≤ g or all four ports are far.
- `AdamEdgeIdentity189.lean`: exact adjacent-edge counting identity (subtraction moved to the opposite side), and n ≤ 3d when a distance-four opposite-terminal port of the same orientation exists on both sides.
- `AdamNearEdge189.lean`: exact near-side specialization, one-bad-vertex witness, and the resulting bound using two independently counted Boolean gains.
- `OtherCentres189.lean`: replacement centres at odd distance with terminal-distance gaps up to three, including mixed selections and the exact rare failure criterion.
- `AdamEdgeLemmaT189.lean`: conditional Lemma T, using the preceding Tight, TPartition, and TEconomy modules. For d ≥ 6 the mirrored near conditions imply n ≤ 3d. The verified statement requires only x, p and q to be high, and no within-shore connectivity.
- `EvenDiameterTwoConnected189.lean`: diameter at most d+1 for vertex connectivity at least two and an even-distance cap d+1. The degree hypothesis is unnecessary.
- `SixCentreParity189.lean` and `SixCentreCount189.lean`: checked arithmetic and incidence-accounting lemmas.

The unrestricted near-side case remains open. This package does not certify the reported CP-SAT or blow-up experiments.

Replay with Lean 4.19.0 and Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b. From a project with that Mathlib dependency, run `lake env bash /path/to/replay.sh`. To also check the diameter theorem, supply `--diameter` and make the established `SmallSeparator189.olean` from [the prior proof](https://github.com/vjdad4m/maths/tree/424c0803dfeb6059ae6085d5ca50cbf30c1d971a/graffiti-189/src) available on LEAN_PATH. The final declarations use only the standard Lean axioms listed in the strict log.
