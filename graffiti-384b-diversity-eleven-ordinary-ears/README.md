# Graffiti.pc #384b: diversity eleven, ordinary two-ear branch

This is a partial result. The exact bound holds on a triangle-supported
finite simple graph with 11 triangle-count types, nine vertices of degree
at least three, and eleven of degree at least two, when its two degree-two
vertices are nonadjacent. Connectedness is not required. For disjoint ear
neighborhoods the proof uses `TriangleFrame.two_ears_equal_quota`;
for overlapping neighborhoods their union has size at most three and
the checked six-vertex selector supplies the extra omission.

The last theorem lifts the branch exclusion to the original problem: any
diversity-eleven failure has a score-preserving supported spanning
counterexample with nine high vertices and either ten nonisolates or
eleven nonisolates in which the two low vertices are the degree-two
vertices of a single pendant triangle. Neither remaining case is claimed
here.

## Replay
Use original Lean and Mathlib v4.19.0 and the dependency closures for
`graffiti-384b-diversity-eleven-twelve` and
`graffiti-384b-private-triangle-extension`.
These closures use two module names for a shared declaration family.
The `CliquePivot33` source subsumes the `ShoreCliquePivot` interface,
whose declaration region is identical; rebuild the one-line source
`compat/ShoreCliquePivot.lean` into a fresh, higher-priority import
directory, thus aliasing that module without introducing any new
declarations or changing the archives. Compile, in order:
1. `compat/ShoreCliquePivot.lean`
2. `src/DiversityElevenOrdinaryEars384b.lean`
3. `src/DiversityElevenPendantResidual384b.lean`.

Use `-j1 -s32768 -DElab.async=false -DwarningAsError=true` with the
corresponding source root and output `.olean` file on `LEAN_PATH`.
`StrictReplay.log` records the check. All results use only standard axioms.
