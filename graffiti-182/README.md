# Graffiti.pc #182: the periphery of the square

For a finite simple connected graph $G$ on at least two vertices, the [catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf) asks for

$$L_s(G)+b(G)\ge\Delta(G^2[B(G^2)])+\operatorname{diam}(G),$$

where $B(G^2)$ is the set of vertices of maximum eccentricity in the square. The graph inside $\Delta$ is the induced subgraph on that set.

The right-hand side is at most $n+2$. The standard $n+1$ bound for $L_s+b$ handles all cases except the metric equality case. There, the original diameter is four and every vertex is peripheral in the square, and a pair at original distance three has square distance two. Thus the original diameter is at most twice the square radius, and the peripheral degree is at most the maximum degree of the square. The [#183 theorem](../graffiti-183/README.md) gives the required bound.

[Lean theorem](Proof182.lean) · [Reduction to #183](Bridge182.lean)

## Replay

From a Lean 4.19.0 / Mathlib 4.19.0 project:

    lake env bash /path/to/maths/graffiti-182/replay.sh
