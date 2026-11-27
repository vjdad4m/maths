# Graffiti.pc #189 for triangle-free 2-connected graphs

**The general conjecture remains open.** This proves the full triangle-free, 2-connected case for every degree threshold: if at most one vertex has degree below $d$ and each vertex is at even shortest-path distance from at most $d+1$ vertices, including itself, then the graph has a Hamiltonian path.

The precise statement is [`triangle_free_traceable_all_degrees`](src/TriangleTrace189.lean). [TriangleFree189.lean](src/TriangleFree189.lean) separately verifies the sharper order bound $|V(G)|\le2d+2$ for $d\ge3$. The traceability proof does not invoke an unformalized small-order theorem.

## Proof

Choose a vertex $v$ of degree at least $d$ and put $A=N(v)$ and $B=N_2(v)$. The triangle-free hypothesis makes $A$ independent. The distance-two budget gives $d\le|A|\le d+1$ and $d-1\le|B|\le d$. Each $b\in B$ has at most $d-|A|+1$ neighbors outside $A$: a neighbor $a\in A$ already sees the other $|A|-1$ vertices of $A$ at distance two, and it sees each of those additional neighbors there too.

If a third layer exists, $|A|=d$. At least two vertices of $B$ touch the third layer, and one of them has degree at least $d$. Every high-degree vertex of $B$ with a neighbor outside $A$ must use the same outward neighbor, since its neighborhood in $A$ overlaps the first such vertex's neighborhood. This also makes $B$ independent. A possible second third-layer vertex would have degree at most two, giving a second low-degree vertex; the even-distance budget and 2-connectivity rule out a fourth layer once the third is a singleton.

When the third layer is a singleton $z$, the bipartition is $A\cup\{z\}$ and $\{v\}\cup B$. If there is no third layer, use $A$ and $\{v\}\cup B$. If the latter case has an edge internal to $B$, its existence forces $|A|=d$ and $|B|=d$, and one of its endpoints is the unique low-degree vertex. Retaining only the crossing edges leaves a near-balanced bipartite spanning subgraph. Every vertex in the smaller part still has degree at least $d$, and all vertices of the larger part have degree at least one.

In each case, the balanced graph, or the graph balanced by adding one universal dummy on the smaller side, satisfies the bipartite degree-sum criterion of [Moon and Moser (1963)](https://doi.org/10.1007/BF02759704). The Lean proof [checks that criterion by closure](src/BipartiteOre189.lean) and removes the dummy vertex if used to obtain the desired path. The $d\le2$ case follows from the [previous small-separator bound](../graffiti-189/src/SmallSeparator189.lean).

## Context and replay

See the [Written on the Wall II catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf) for #189 and [Easwar and Johari](https://arxiv.org/html/2609.11719v1) for earlier partial results, including traceability up to order $2d+2$. No priority claim is made.

From a Lean 4.19.0 project with the Mathlib 4.19.0 build cache:

    lake env bash /path/to/maths/graffiti-189-triangle-free/replay.sh
