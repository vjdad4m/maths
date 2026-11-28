# Graffiti.pc #384b: the dense pendant board with exactly three tags

This is an exact partial theorem at triangle-count diversity eleven.
In the supported spanning graph, take the order-eleven configuration
with two degree-two vertices comprising one pendant triangle and nine
high (degree at least three) vertices. Its eight nonanchor highs form
a minimum-degree-three board. The conjectured 2-domination bound holds
if exactly three vertices of that board miss the anchor.

The theorem `exact_pendant_three_tags` is for the actual graph (not a
bit-mask model). The final `residual_eleven_ten_or_four_to_six_tags`
reduces any original diversity-eleven failure to a score-preserving
supported spanning failure, with nine highs and either ten nonisolates
or eleven nonisolates with the pendant triangle, connected dense
eight-high board, and four to six zero tags. Those cases remain open.

## What Lean checks

1. A closed 323-addition RUP proof produces an actual Lean proof of
   contradiction for its 1242 used CNF clauses using the stock Mathlib
   SAT proof-term builder. No native reflection lemma is used.
2. The exact same formula has a candidate graph valuation. Lean checks
   1197 gate rows from elementary Boolean truth tables and 45 root rows
   from exact degree, triangle-score threshold and sorting constraints
   or failure of one of the weighted retained triples.
3. Lean verifies canonical `Fin 8` relabeling of tags by triangle
   counts and of the other labels by their adjacencies to the two
   least-score tags; it proves the circuit adjacency, degree and
   triangle counts match the graph. The three retained vertices are
   transported back to the ambient graph with their exact support
   credit for seeing the pendant anchor.

Only the usual Lean axioms are used. `StrictReplay.log` includes the
axiom audits. Python and the SAT solver produce candidate data only;
the verification theorem does not require trusting their computations.

## Replay

Use Lean/Mathlib v4.19.0. Bring the object closures of the existing
`graffiti-384b-diversity-eleven-pendant-tags`,
`graffiti-384b-diversity-eleven-dense-pendant`, and
`graffiti-384b-diversity-eleven-ordinary-ears` packages, including
the ordinary-ears one-line compatibility overlay. Additional existing
modules are `EffectiveSearchScore384b` and `Q8Original384b` (both
also predecessor modules of diversity eleven's order-twelve package).

Make sure stock `Mathlib/Tactic/Sat/FromLRAT.lean` at the same Mathlib
pin has a built .olean in the first Mathlib overlay on LEAN_PATH, and
that `Mathlib.Data.Fin.Tuple.Sort` is available there. Compile the
following files from `src/`, in order, with
`-j1 -s32768 -DElab.async=false -DwarningAsError=true`, and put each
output .olean in a single package directory on LEAN_PATH. Keep the
included `q11-study` certificate paths as distributed.

- `DiversityElevenMathlibRup384b.lean`
- `DiversityElevenCircuitBits384b.lean`
- `DiversityElevenPendantRupThree384b.lean`
- `DiversityElevenPendantWires3384b.lean`
- `DiversityElevenPendantWireClauses3384b.lean`
- `DiversityElevenPendantThresholds3384b.lean`
- `DiversityElevenPendantSemanticRoots3384b.lean`
- `DiversityElevenPendantFinite384b.lean`
- `DiversityElevenNormalizeThree384b.lean`
- `DiversityElevenPendantCounterThree384b.lean`
- `DiversityElevenExactThreeSelector384b.lean`
- `DiversityElevenExactThreePendant384b.lean`
- `DiversityElevenFourTagResidual384b.lean`

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
