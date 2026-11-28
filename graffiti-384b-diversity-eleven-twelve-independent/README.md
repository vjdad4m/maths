# Graffiti.pc #384b: the independent-low part of the 12-nonisolated profile

The conjectured bound holds at diversity eleven for finite simple
triangle-supported graphs with twelve nonisolated vertices and nine
vertices of degree at least three, provided the nonisolated low
vertices are independent and the high triangle counts are distinct
and at least two. The score conditions hold in any hypothetical
counterexample in this profile by the earlier `split_profile`.
No graph enumeration or connectivity assumption occurs in this branch.

Proof: the three independent low vertices are ordinary ears. If their
collective footprint has at most five high vertices, omit three
untouched highs using the earlier result. Otherwise the three ear
anchor pairs are disjoint. Try omitting the untouched triple. A
failure implies an untouched cubic x adjacent to both other untouched
vertices y,z and one marked vertex a. The two other untouched vertices
are noncubic, since two cubics with distinct scores at least two
cannot be adjacent. Exclude a's marked pair. For either y or z, at least
one of the other two marked pairs can be simultaneously omitted with
x and that vertex, as far as the chosen noncubic is concerned: it can
block at most one pair. If both of those chosen swaps fail at a marked
anchor, each blocking anchor would have triangle score at most two.
They would therefore be the same high vertex and belong to the same
marked pair, but the two failures would force incompatible locations
for its additional high neighbor. One swap gives six omitted vertices.

Main declarations:
- `Graffiti384b.DiversityEleven.exact_of_three_matched_cubic_fallback`.
- `Graffiti384b.DiversityEleven.exact_twelve_independent`.

The 12-nonisolated pendant case and the full diversity-eleven
conjecture are not claimed in this package.

## Replay

Lean 4.19.0 (6caaee842e94), Mathlib v4.19.0
(c44e0c8ee63ca166450922a373c7409c5d26b00b). Put the previously
checked diversity-eleven-thirteen, large-lower, lower and structure
object directories, and their documented transitive prerequisites
(including `ShorePairs` and `FixedCubics`), on `LEAN_PATH`.
Run `lake env bash /path/to/this/package/replay.sh`.
The strict check uses only `propext`, `Classical.choice`, and `Quot.sound`.
