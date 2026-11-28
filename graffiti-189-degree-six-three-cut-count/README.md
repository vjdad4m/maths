# Graffiti.pc #189: component and port restrictions at a three-cut when d=6

Let G be a finite connected simple graph, with at most seven
even-distance vertices (including the root) at each vertex and with
at most one vertex of degree below six. Assume deleting fewer than
three vertices preserves connectivity. Then an arbitrary deletion
of three vertices leaves at most three components. This is a strict
Lean restriction on exact connectivity three, not a spanning-path
proof for the remaining graph class.

The main checked definition is
`Graffiti189LongestPath.ThresholdSix.ThreeCut.three_cut_at_most_three_components`.
Every actual deletion component is realized by a nonempty closed
finite shore. For four such shores, high ports at one terminal
would require four local costs of at least four. Summing the other
three shores' port counts against the distance-two cap limits
total ports to eight, and the local distance-two accounts cap at
six, a contradiction. Otherwise the unique low vertex is a port
for every terminal, and its distance-two cap cannot accommodate
three visible vertices from each of the other three shores.

The separate checked theorem
`not_three_high_port_shores_at_isolated_terminal` concerns a vertex
of the cut that has no internal edge to either of the other two
cut vertices. If there are three internally connected shores, at
least one of them lacks a degree-six port at that terminal. Each
second cut neighbor of a selected port consumes a distance-two
slot at the terminal, so the three shores have at least eight
ports in total but at most four local distance-two slots. A
saturated foreign port count forces its chosen port to see its
whole shore. The tight counts give either one four-vertex shore
with two low nonports or two such shores with one low each.

## Replay

Lean v4.19.0 and the same pinned Mathlib as the checked
[CrossSaturation189](../graffiti-189-cross-saturation/) and
[AdjacentCutFiveActual189](../graffiti-189-adjacent-cut-structure/)
modules are required. Put those existing object closures and this
package's object directory on LEAN_PATH. Compile the following
under the source root `src` in order, for example with
`-j1 -s32768 -DElab.async=false -DwarningAsError=true`:

1. `SixTripleCutBasics189.lean`
2. `SixTripleCutFourShore189.lean`
3. `SixTripleCutComponents189.lean`
4. `SixTripleCutIsolate189.lean`

Strict replay and audits use only the standard Lean axioms and
are recorded in `StrictReplay.log`.
