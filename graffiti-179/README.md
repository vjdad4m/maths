# Graffiti.pc #179: both degree conventions

For a finite simple connected graph on at least two vertices, Lean verifies
$$L_s(G)+b(G)\ge \Delta(G)+\gamma(G)+\lambda_{\max}(G).$$
Here $L_s$ is the maximum number of spanning-tree leaves, $b$ is the maximum
order of an induced bipartite subgraph, $\Delta$ is the maximum degree,
$\gamma$ is the domination number, and $\lambda_{\max}$ is the maximum
independence number of a vertex neighborhood.

The [printed catalogue, p. 104](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf)
displays minimum degree $\delta$.
[Douglas West’s register](https://dwest.web.illinois.edu/regs/graffiti.html)
records the stronger formula with $\Delta$, which implies the printed one.
[Strong179.lean](Strong179.lean) checks both formulas. The
[earlier formalization](Proof179.lean) of the printed bound is retained
for its separate spanning-tree and induced-bipartite development.

## Proof

Choose a vertex $v$ with an independent subset $A$ of its neighbors of size
$\lambda_{\max}$. Extend $\{v\}$ to an inclusion-maximal independent set $B$.
The maximality of $B$ makes it dominating, so $|B|\ge\gamma$. Since $v\in B$,
none of its neighbors in $A$ can belong to $B$. The union $A\cup B$ is thus
induced bipartite and $b\ge\lambda_{\max}+\gamma$.

The star at a maximum-degree vertex extends to a spanning tree. Every tree
on at least two vertices has at least as many leaves as the degree of any
vertex, so $L_s\ge\Delta$. Add the two inequalities.

## Lean replay

From a Lean 4.19.0 / Mathlib 4.19.0 project:

```sh
lake env bash /path/to/maths/graffiti-179/replay.sh
```

The script rebuilds the repository dependencies and checks both proof
modules with warnings as errors. The axiom reports for the new theorems
contain only `propext`, `Classical.choice`, and `Quot.sound`.
