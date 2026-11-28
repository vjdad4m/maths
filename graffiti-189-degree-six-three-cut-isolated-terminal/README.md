# Graffiti.pc #189, d=6: three-cuts with an isolated terminal

For a finite connected graph in the degree-six Graffiti hypotheses,
assume deleting fewer than three vertices preserves connectivity.
If a three-vertex deletion set has an isolated vertex internally,
deleting that set leaves at most two components. In particular,
any actual separating set of three vertices inducing zero or one
edge leaves exactly two components.

The top theorem is
`Graffiti189LongestPath.ThresholdSix.ThreeCut.three_cut_at_most_two_of_isolated_terminal`.
For a singleton shore, the other two shores each have two ports
at the isolated terminal, and both ports see all three cut vertices.
One of these ports then has four foreign distance-two vertices and
at least three local ones. For nonsingleton shores, the unique low
vertex is the isolated terminal's sole port in one shore; a universal
port must occur in another. The port counts are (1,2,4) and local
distance-two counts (1,3,0) at the selected terminal. A high port of
the middle shore has five foreign and at least two local distance-two
vertices, also exceeding six.

This constrains three-cut structure; it does not give a spanning
path for the remaining cases.

## Replay

Use Lean/Mathlib v4.19.0 with the
[independent-three-cut package](../graffiti-189-degree-six-independent-three-cut/)
and [degree-five three-connected package](../graffiti-189-degree-five-three-connected/)
on LEAN_PATH, including their predecessor object closures. Compile
from `src/` in order using
`-j1 -s32768 -DElab.async=false -DwarningAsError=true`:

1. `SixTripleCutSingletonNoIsolate189.lean`
2. `SixTripleCutUniversalBudget189.lean`
3. `SixTripleCutNonSingletonIsolate189.lean`
4. `SixTripleCutIsolateComplete189.lean`

`StrictReplay.log` records only standard Lean axioms. No solver
or graph enumeration is used.
