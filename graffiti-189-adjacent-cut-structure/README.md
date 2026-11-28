# Graffiti.pc #189: 5-degree threshold, adjacent actual two-cut

All four module files replayed with Lean 4.19 and warningAsError.
No custom axioms, sorry or native_decide. Run `./replay.sh` with Lean 4.19 on PATH and compatible Mathlib and CrossSaturation189 build directories on LEAN_PATH.

Under `∀ x, (EvenFrom G x).card ≤ 6`, connectedness after deleting fewer
than two vertices, and an adjacent separating pair `a,b`:
- Exact actual-cut order bound: `Fintype.card V ≤ 21`. If a,b are
  true twins, the bound is 17. The order bounds do not need degree hypotheses.
- With all but at most one vertex of degree at least 5, exactly 2 or 3
  genuine components remain. The theorem excludes four or more.
- For either orientation, `order + number of exclusive a-ports ≤ 22`
  (the cut vertices themselves are not ports). Hence at order 21 each
  color has at most one exclusive port; at order 20 each has at most two.

The order bound adapts the published adjacent-cut geometry: four
positive-even sets cover all non-cut vertices; asymmetric cut ports
make overlaps, while twins make the two cut centers redundant.
Distinct a-exclusive ports each make a distinct overlap using an
opposite-side a-port.

The component bound uses the actual induced components and counts
only internal degree augmented by the two cut terminals. Four
components cannot include an entirely high order-four shore: it
would be four common ports, and a port on another shore sees all four
and one same-color port from each of two further shores at distance
two. The total order cap then forces either a low singleton or shore
orders 4,5,5,5. The low singleton is a common port and sees two visible
ports in each other shore at distance two; a nonsingleton shore must
have two by singleton-deletion connectivity. In the other case the
three high order-five shores consist entirely of visible ports,
but at most five of each color are possible, counting from the
order-four shore.

None of this asserts traceability yet. The published exact
distance-two package can close a subsidiary separating pair if it
has distance two, but cannot directly be applied to an adjacent pair.
An additional paper lead: if a nonsingleton shore has exactly two
visible ports and at least one interior vertex, those two ports are
a new genuine two-cut with a strictly smaller shore. Thus a
minimal-shore adjacent-cut analysis can discard this pattern if all
nonadjacent genuine cuts are already dispatched. A separate route
argument is still needed for the remaining two- and three-component
cases.
