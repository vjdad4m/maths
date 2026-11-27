# Graffiti.pc #184 is false

The [catalogue statement](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf) uses the mean in $G^2$ over ordered pairs with a peripheral first vertex and a distinct second vertex. The [Lean certificate](Counterexample184.lean) uses the same explicit 22-vertex graph as [#185](../graffiti-185/README.md). Its maximum spanning-tree leaves plus largest induced bipartite order is at most $24$.

The square has maximum degree 21 and diameter two. The only universal vertex is $r$, so the 21 other vertices constitute the periphery. They contribute 441 ordered pairs at positive distance, including every one of the 234 ordered pairs at distance two. The mean is therefore $675/441=75/49$. The right-hand side is $21+2\cdot75/49=24+3/49$, strictly above 24.

No claim is made that this is a smallest counterexample.

## Replay

From a Lean 4.19.0 / Mathlib 4.19.0 project:

    lake env bash /path/to/maths/graffiti-184/replay.sh
