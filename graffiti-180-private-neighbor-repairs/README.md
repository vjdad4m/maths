# Graffiti.pc #180: the bipartite-lower transition and private-neighbor repairs

Lean checks that when the lower graph in the stated tight horizontal
triangle transition is bipartite, rooted sparsity and the rank drop force
it to be a tree. Biconnectivity of the upper graph then reduces it to a
triangle, and neither orientation admits a second-form certificate.
Thus a remaining tight transition on at least four vertices must have
a nonbipartite lower graph.

Separately, for a two-connected old core, the proof gives an exact
two-vertex repair criterion under the stated attachment hypotheses.
When the two failed releases each have one private leaf, successful
returns are exactly the common neighbors of those leaves that meet the
retained core. A checked 14-vertex example has a unique such return.
It satisfies #180 and fails the tight rooted-sparse assumptions, so it
is not an obstruction to the catalogue conjecture.

See `NoBipartiteSecond180.lean`, `DetachedPair180.lean` and
`DetachedScope180.lean`. The nonbipartite branch and the full conjecture
remain open.

Use Lean 4.19.0 with Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
on `LEAN_PATH`, then run `bash graffiti-180-private-neighbor-repairs/replay.sh`.
