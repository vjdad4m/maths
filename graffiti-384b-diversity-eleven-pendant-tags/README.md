# Graffiti.pc #384b: connected pendant board and zero-tag restrictions

Partial result for diversity eleven. Work on the triangle-supported
spanning graph, with nine high vertices of degree at least three. The
order-eleven branch (nonisolates) has exactly one pendant triangle on
a high anchor. The other eight high vertices make the board. A board
vertex is zero-tagged if it misses the anchor.

The theorem `residual_eleven_ten_or_three_to_six_tags` says an original
diversity-eleven counterexample would give a score-preserving, supported
spanning counterexample either with ten nonisolates, or with precisely
the pendant configuration above, such that the eight-vertex board
has internal minimum degree at least three, has no nonempty
anticomplete partition, and has three through six zero tags.

Why these new restrictions hold:
* A nontrivial split forces two four-cliques. Adjacent ambient cubics
  cannot realize distinct triangle scores at least two, so each clique
  has at most one zero tag. Keep that vertex or an arbitrary member.
* The anchor has at least two triangles incident to it. A triangle
  besides the pendant triangle gives two adjacent nonzero board vertices.
* With one or no zero tags, keep a prescribed board vertex (the tag
  if it exists). There are at most four uncovered vertices, each
  forbidding at most three of the 21 possible pairs of extra kept
  vertices. A pair not forbidden by any uncovered vertex suffices.
* With two tags, keep both. There are at most three unresolved vertices
  in the six remaining; otherwise the tags would be adjacent ambient
  cubics. The three unresolved vertices each forbid at most two choices
  for the third kept vertex. Their bad sets cannot cover all six:
  any hypothetical cover forces a repeated forbidden choice, by
  symmetry and looplessness of the nonadjacency relation on distinct
  members of the unresolved set.

No SAT or exhaustive graph enumeration is used in this package.

## Replay

Use Lean/Mathlib v4.19.0 and the prior
`graffiti-384b-diversity-eleven-dense-pendant` and
`graffiti-384b-diversity-eleven-ordinary-ears` packages, including the
latter's one-line compatibility overlay for `ShoreCliquePivot`.
Compile `.lean` modules in `src` in this order:
1. DiversityElevenPendantSplit384b
2. DiversityElevenPendantTags384b
3. DiversityElevenPendantOneTag384b
4. DiversityElevenOneCenter384b
5. DiversityElevenPendantTwoTags384b
6. DiversityElevenPendantTagResidual384b

Use `-j1 -s32768 -DElab.async=false -DwarningAsError=true`. Each output
olean must be on `LEAN_PATH`. Axiom output is in `StrictReplay.log`.
