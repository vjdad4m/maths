# Graffiti.pc #180: sufficient conditions for two-vertex exchanges

Lean formalizes sufficient bridge and path conditions for repairing a
certificate after the failure of a single-vertex exchange. The bridge
theorem applies when the failed tip sees every other vertex of the
certificate and the eligible bridge endpoints each have a surviving
neighbor dominating their other surviving neighbors. It exchanges two
certificate vertices for the bridge endpoints, avoiding both chord
endpoints and gaining one eligible leaf.

The bridge theorem repairs both orientations of the previously certified
14-vertex single-exchange obstruction. The separate absorbed-gate condition
repairs the specified 12-vertex example. These are positive results under
explicit hypotheses, not a proof that two-vertex exchanges always work,
and not a solution of #180.

See `Minimal180.Controlled.pair_of_bridge_ports` in
`src/BridgePair180.lean` and the checked examples in
`src/BridgeExample180.lean` and `src/AbsorbedExample180.lean`.

Use Lean 4.19.0 with Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
and an existing Mathlib `LEAN_PATH`. From the repository root run
`bash graffiti-180-controlled-pair-exchanges/replay.sh`.
