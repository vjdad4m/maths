# Graffiti.pc #384b: the dense pendant board with exactly four tags

This is an exact partial theorem at triangle-count diversity eleven.
The supported-graph theorem `exact_pendant_four_tags` proves the
conjectured 2-domination bound for the dense eight-high pendant board
when exactly four board vertices miss the high anchor.
`residual_eleven_ten_or_five_six_tags` reduces any original failure at
diversity eleven to a score-preserving triangle-supported spanning
failure with nine high vertices and either ten nonisolates or eleven
nonisolates with a pendant triangle, connected dense eight-high board,
and five or six vertices missing the anchor.

As in the preceding three-tag result, Lean checks both the RUP
contradiction and the complete gate and graph semantics. This case
uses 783 RUP additions and 2565 used initial clauses, of which 2490
are local gate clauses and 75 are degree/score/order or retention roots.
The checks use only standard Lean axioms, not native evaluation.

## Replay

Start from the checked dependency closure of
`graffiti-384b-diversity-eleven-three-tag`, retaining the same
Lean/Mathlib v4.19.0 and its required Mathlib and compatibility
overlays. Place the following output objects on LEAN_PATH and compile
these sources in order with
`-j1 -s32768 -DElab.async=false -DwarningAsError=true`.
Keep certificates in their distributed relative paths, invoked by
ordinary `include_str`.

- `DiversityElevenNormalizeTags384b.lean`
- `DiversityElevenPendantRupFour384b.lean`
- `DiversityElevenPendantWires4384b.lean`
- `DiversityElevenPendantWireClauses4384b.lean`
- `DiversityElevenPendantThresholds4384b.lean`
- `DiversityElevenPendantSemanticRoots4384b.lean`
- `DiversityElevenPendantCounterFour384b.lean`
- `DiversityElevenExactFourSelector384b.lean`
- `DiversityElevenFiveTagResidual384b.lean`

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
