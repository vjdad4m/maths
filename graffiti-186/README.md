# Graffiti.pc #186: literal and external neighborhoods

The [literal catalogue statement](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) is [false in Lean](Counterexample186.lean). Write $C$ for the center of the square graph $G^2$, and let $N(C)$ be the union of the open neighborhoods of the vertices of $C$ in $G^2$. This union can contain vertices of $C$. Its use in the catalogue cannot be replaced silently by the external neighborhood.

The separate inequality with the **external** neighborhood is [true in Lean](External186.lean). For a finite simple connected graph of order $n\ge2$,

$$|N(C)\setminus C|+2\max_{v\in V(G)} d_{G^2}(v,C)\le n+1\le L_s(G)+b(G).$$

Here $d_{G^2}(v,C)$ is the minimum distance from $v$ to a center vertex, $L_s$ is the maximum number of spanning-tree leaves, and $b$ the largest induced bipartite order. For the published 13-vertex witness, the literal metric side is 16; using the external neighborhood reduces it to 12.

## Proof

Let $h=\max_v d_G(v,C)$. The distance in the square is the original distance rounded up after division by two. Hence the square set eccentricity is $\lceil h/2\rceil$. A shortest path from $C$ to a farthest vertex gives $\max(0,h-2)$ distinct vertices outside both $C$ and its square neighborhood. Their count, plus $|C|$ and $|N(C)\setminus C|$, is at most $n$.

When $|C|\ge2$, this gives the stated metric bound directly. When $C=\{c\}$, $h$ is even: if it were odd, any original neighbor of $c$ would have original eccentricity at most $h+1$, and therefore square eccentricity at most that of $c$. It would also be a square center, a contradiction. The even case gives the same bound. The remaining inequality $n+1\le L_s+b$ is the [DeLaViña–Waller bound](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v15i1r33/pdf), rechecked in the repository's [#179 development](../graffiti-179/Proof179.lean).

## Replay

From a Lean 4.19.0 / Mathlib 4.19.0 project:

    lake env bash /path/to/maths/graffiti-186/replay.sh

Both statements are checked with warnings as errors; the final theorems use only the three standard Lean axioms.
