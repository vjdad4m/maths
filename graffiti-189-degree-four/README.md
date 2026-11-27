# Graffiti.pc #189: the degree-four bound with at most three second neighbors

The [Lean proof](src/SharpThreeClose189.lean) constructs a Hamiltonian path in a finite 2-connected graph if all but at most one vertex have degree at least four, each vertex has at most five even-distance vertices (including itself), and each vertex has at most three vertices at distance exactly two. Under the first two count bounds, radius at least four automatically implies the last hypothesis. This covers the radius-at-least-four case of Graffiti.pc #189 at second-smallest degree four. It does not settle the unrestricted conjecture.

The proof follows the longest-path attachment argument in the [earlier degree-three release](../graffiti-189). In this case a nonspanning longest path would leave one omitted component. Each active vertex in that component attaches to one path vertex. Chords and distance-two counts force all omitted vertices to be active, and any edge between different attachment classes forces both endpoints to be adjacent to all other omitted vertices. The distance-two budgets at the attachment vertices then force the omitted component to have at most two vertices, contradicting the degree condition.

## Replay

From a Lean 4.19.0 project with the Mathlib 4.19.0 build cache:

    lake env bash /path/to/maths/graffiti-189-degree-four/replay.sh
