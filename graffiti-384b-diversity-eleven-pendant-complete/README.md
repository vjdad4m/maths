# Graffiti.pc #384b: every eleven-nonisolated diversity-eleven branch

The checked theorem `residual_eleven_exactly_ten` reduces every
diversity-eleven failure to a score-preserving triangle-supported
spanning failure with exactly ten nonisolates and nine vertices of
degree at least three. No original connectivity premise is required.
Every other supported order has been excluded by this package and
its dependencies.

In particular, the two remaining dense pendant board cases, with five
or six of its eight board vertices missing the high pendant anchor,
are now exact. The earlier packages dealt with orders twelve and
above, the ordinary ear pairs, the low-degree and disconnected
pendant boards, and zero through four vertices missing the anchor.
The ten-nonisolated branch is not proved here, and the unrestricted
conjecture is not proved here.

## Certificates

The five-tag sliced proof has 1681 RUP additions and 3837 used input
clauses, 3750 circuit gate clauses and 87 semantic roots. The analogous
six-tag proof has 3106 additions and 4877 inputs, 4779 gates and 98
semantic roots. Lean proves the exact semantic adaptation of each
count, ordering, and weighted retained-triple condition. The same
proofs include the normalization, adjacency, score and neighborhood
support lifts to the actual finite simple graph.

To keep kernel memory bounded, `DiversityElevenModularRup384b` uses
the standard Mathlib proof-step construction, declaring each learned
clause as an independently kernel-checked theorem rather than
inlining its proof expression into a single large proof DAG. No native
reduction is used to accept proofs. All audited results use only
standard axioms; untrusted solver/Python outputs are certificates.

## Replay

Use Lean/Mathlib v4.19.0 with the dependencies and overlay instructions
from the checked `graffiti-384b-diversity-eleven-four-tag` package
and its prerequisites, including the one-line compatibility alias for
`ShoreCliquePivot` and the rebuilt stock `Mathlib.Tactic.Sat.FromLRAT`.
Compile the following files from `src/` in order, with all output
objects on LEAN_PATH, using
`-j1 -s32768 -DElab.async=false -DwarningAsError=true`.
Preserve the relative `q11-study/` paths for the archived certificates.

- `DiversityElevenModularRup384b.lean`
- `DiversityElevenPendantRupFive384b.lean`
- `DiversityElevenPendantWires5384b.lean`
- `DiversityElevenPendantWireClauses5384b.lean`
- `DiversityElevenPendantThresholds5384b.lean`
- `DiversityElevenPendantSemanticRoots5384b.lean`
- `DiversityElevenPendantCounterFive384b.lean`
- `DiversityElevenExactFiveSelector384b.lean`
- `DiversityElevenPendantRupSix384b.lean`
- `DiversityElevenPendantWires6384b.lean`
- `DiversityElevenPendantWireClauses6384b.lean`
- `DiversityElevenPendantThresholds6384b.lean`
- `DiversityElevenPendantSemanticRoots6384b.lean`
- `DiversityElevenPendantCounterSix384b.lean`
- `DiversityElevenExactSixSelector384b.lean`
- `DiversityElevenNoPendantResidual384b.lean`

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and follow the replay instructions above.
