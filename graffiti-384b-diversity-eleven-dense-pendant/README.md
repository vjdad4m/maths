# Graffiti.pc #384b: internal degree two in the diversity-eleven pendant branch

This is a partial result. For a triangle-supported finite simple graph with
11 triangle-count types and nine vertices of degree at least three,
suppose its two degree-two vertices form a pendant triangle on a high
anchor. The exact conjectured bound follows when the eight nonanchor
highs have a vertex of internal degree two.

The board vertex in question is ambient cubic and sees the anchor.
Distinct rich triangle scores prohibit a cubic neighbor of this vertex.
Keep the anchor and one board neighbor of the cubic, and omit the cubic.
On the six remaining board vertices use the checked six-selector. A
vertex with no fixed retained neighbor loses no triangles: if a lost
triangle uses the cubic, its third vertex must be the anchor or the
other retained vertex. Vertices with one fixed supporter retain internal
degree at least two. This does not require board or ambient connectivity.

The integrated `residual_eleven_ten_or_dense_pendant` theorem reduces
each original diversity-eleven failure to a supported spanning
score-preserving failure with nine highs, either of order ten after
isolates are removed or of order eleven with the stated pendant triangle
and internal minimum degree at least three on its eight nonanchor highs.

## Replay

Use Lean/Mathlib v4.19.0, with objects from
`../graffiti-384b-diversity-eleven-ordinary-ears/`,
`../graffiti-384b-diversity-eleven-twelve/`, and the original
transitive dependencies. Use the compatibility alias provided in the
ordinary-ears package in the overlay resolving `ShoreCliquePivot`.
Compile in this order (each name has a `.lean` suffix in `src`):

1. DiversityElevenPendantBoard384b
2. DiversityElevenPendantGeometry384b
3. DiversityElevenSixTriangleRange384b
4. DiversityElevenPendantSix384b
5. DiversityElevenPendantCubic384b
6. DiversityElevenPendantDenseResidual384b

Use `-j1 -s32768 -DElab.async=false -DwarningAsError=true`; write each
object into the same fresh overlay `.olean` lookup directory. All audited
theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
