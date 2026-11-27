# Graffiti.pc #189: the 2-connected degree-three case

**The general conjecture remains open.** The Lean theorem in [CloseD3189.lean](src/CloseD3189.lean), `traceable_d3_two_connected`, proves the following stronger formulation of the degree-three case:

> Every finite simple 2-connected graph has a Hamiltonian path if at most one vertex has degree below three and every vertex has at most four vertices at even shortest-path distance, counting itself.

The [Written on the Wall II catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf) asks whether a connected graph is traceable if its maximum even-distance count is at most one plus its second-smallest degree. The distance-zero vertex counts, and degree ties count with multiplicity. [Easwar and Johari, Theorem B](https://arxiv.org/html/2609.11719v1) give several other sufficient conditions, including graphs that are not 2-connected. We do not invoke their theorem in the Lean proof.

## Proof outline

Take a nonspanning longest path, rotating if needed so both endpoints have degree at least three. A vertex outside this path that touches the path is called active, and its neighbor on the path is its pin. The distance-two budget bounds the size of the separator around an active vertex and its neighbors outside the path. When the budget is tight, each active vertex has exactly one pin, and the two path vertices immediately before and after that pin exhaust the distance-two vertices outside the separator. The flanks are unchanged by rotations that keep the same vertex set.

The tight budget also gives each active vertex eccentricity at most three. The proof shows that the complement of the path is connected and has at least three vertices. It has at least two distinct pins. Choose a pair of differently pinned active vertices with minimum distance in the complement. Each side has two path flanks using up two distance-two slots:

- If the active vertices are adjacent, the other pin takes up the remaining slot. Both active vertices are then universal in the omitted component, which uses only the two pins. Each pin has at least two distance-two vertices already on the path, so it misses at most one omitted vertex. The disjoint pin neighborhoods cannot cover three omitted vertices.
- At distance two, the two active vertices exhaust each other's remaining slot. Their closed neighborhoods in the omitted component cover it. One common neighbor and two disjoint flank pairs leave no room for any further groups: any additional vertex in one neighborhood would necessarily be active but would be too far from the other pin. The remaining three-vertex omitted path would have all degrees below three.
- At distance three or larger, those last slots are already used inside the omitted component. The two pins have only their respective flanks as path neighbors. Any route of length at most three from one active vertex to the other pin would either pass through a vertex with both pins, use a forbidden path edge through the flanks, or find a closer differently pinned active pair. Thus the eccentricity bound fails.

The proof is structural. It does not depend on the separate graph search that motivated the analysis.

## Other checked reductions

[SmallSeparator189.lean](src/SmallSeparator189.lean) also proves traceability whenever vertex connectivity is at least the maximum number of distance-two vertices, and gives refinements when positive even distance layers themselves are separating. [Rigidity189.lean](src/Rigidity189.lean) formalizes the path-rotation constraints, connectedness of the omitted graph in the near-connectivity case, and an order lower bound: if the even-distance allowance is $d+1$, at most one vertex has degree below $d$, and vertex connectivity is at least $d-1$ with $d\ge3$, a nontraceable graph has at least $5d-3$ vertices.

## Replay

From a Lean 4.19.0 project with Mathlib 4.19.0 and its build cache:

    lake env bash /path/to/maths/graffiti-189/replay.sh

The source modules build in a temporary directory with warnings as errors and only standard Lean axioms.
