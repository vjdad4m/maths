# Graffiti.pc #384b: diversity eleven reduces to 10 or 11 nonisolated vertices

For finite simple graphs with eleven distinct vertex triangle-count
types, every triangle-supported profile with nine high vertices and
twelve nonisolated vertices satisfies the exact bound. A vertex is high
if its degree is at least three. In particular any diversity-eleven
counterexample has a spanning triangle-supported counterexample
retaining all triangle counts, with nine high vertices and only 10 or
11 nonisolated vertices. No connectivity assumption is used.

The independent-low branch uses the preceding exact analytic proof.
In the remaining pendant branch, with one ordinary ear and one
adjacent pair of lows, begin with two omitted lows. These touch
at most three of the nine highs, leaving six untouched highs.
Within those six the high vertices with zero external support already
have internally distinct triangle counts at least two and degree
at least three. There is a pair of retained vertices of the six:
every other zero-support vertex sees both, and every other vertex of
internal degree at least two sees at least one. Vertices of internal
degree at most one necessarily already have two external supports.
This proves an extra four omissions beyond the initial two.

The six-vertex selector uses exact graph labelling, a degree-sorting
reduction, and a Boolean bit-mask certificate. All 64 possible
zero-support tags are evaluated together using packed masks.
The 15 adjacency bits are covered by 128 bands, eight bands per
file, with ordinary Lean `decide`. The masks' semantic correctness
is proved independently in Lean. No external graph generator or
native decider participates in replay. Diagnostic scripts are not
part of the proof.

Main declarations:
- `Graffiti384b.DiversityEleven.finite_six_selector`
- `Graffiti384b.DiversityEleven.exact_twelve_supported`
- `Graffiti384b.DiversityEleven.residual_eleven_orders_ten_eleven`

The full diversity-eleven conjecture and general #384b remain open.

## Replay

Use Lean 4.19.0 (6caaee842e94) and Mathlib v4.19.0
(c44e0c8ee63ca166450922a373c7409c5d26b00b). Build prior
diversity-eleven-thirteen and twelve-independent packages and their
transitive prerequisites. The graph-labelling transfer also imports
`Q8Original384b` and `EffectiveSearchScore384b` from the earlier
effective-core/diversity-nine Lean modules. Ensure the pinned Mathlib
module `Mathlib.Data.Fin.Tuple.Sort` is built. Place all object roots
on `LEAN_PATH` and run `lake env bash /path/to/this/package/replay.sh`.
Replay is serial by default; the explicit finite-selector bands may
take substantial time. The allowed axioms are `propext`,
`Classical.choice`, and `Quot.sound`.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
