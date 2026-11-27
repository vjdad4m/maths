# Graffiti.pc #185 is false

The [catalogue statement](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf) asks whether every finite simple connected graph on at least two vertices satisfies

$$L_s(G)+b(G)\ge \Delta(G^2)+2\,\operatorname{avgdist}(G^2).$$

Our 22-vertex graph has left-hand side at most $24$, while the right-hand side is $24+1/77$. [Lean certificate](Counterexample185.lean). No minimum-order or priority claim is made.

## Construction

Take a clique $A$ on nine vertices, a separate clique on a vertex $r$ and six vertices $s_1,\ldots,s_6$, and six private leaves $\ell_i$ adjacent only to $s_i$. Join $r$ to a designated vertex $a$ of $A$. There are no other edges.

- Every spanning tree has $r$, $a$, and all six $s_i$ as internal vertices. The $r$–$a$ bridge is forced, and each endpoint must also connect to its own side. Each $s_i$ connects its private leaf and the rest of the graph. Thus $L_s\le14$.
- An induced bipartite set meets each of the two original cliques in at most two vertices, so even with all six private leaves it has order at most ten.
- In the square, $r$ is universal. The only square nonedges are the pairs of distinct private leaves and the cross pairs between $A$ and the twelve vertices $s_i,\ell_i$, except for the six pairs $a,s_i$. The total is $\binom 62+9\cdot12-6=117$. All these pairs are at square distance two; all other distinct pairs are at distance one. Hence the mean is $1+234/(22\cdot21)=116/77$, and the maximum degree is 21.

## Replay

From a Lean 4.19.0 / Mathlib 4.19.0 project:

    lake env bash /path/to/maths/graffiti-185/replay.sh

The script checks the proof with warnings as errors.
