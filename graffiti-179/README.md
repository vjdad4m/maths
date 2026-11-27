# Graffiti.pc #179: the displayed minimum-degree inequality

For a finite simple connected graph on at least two vertices, Lean
verifies
$$L_s(G)+b(G)\ge \delta(G)+\gamma(G)+\lambda_{\max}(G),$$
where the terms are the maximum number of spanning-tree leaves, the
maximum order of an induced bipartite subgraph, minimum degree,
domination number, and maximum neighborhood independence number.

**Scope.** The [November catalogue, p. 104](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf)
displays lowercase $\delta$. Its glossary lists maximum degree, and
[Douglas West’s register](https://dwest.web.illinois.edu/regs/graffiti.html)
transcribes a stronger version with uppercase $\Delta$. This proof does
not settle the maximum-degree version.

## Proof

Let $A$ be an independent set of size $\lambda_{\max}$ in the neighborhood
of $v$, and $x\in A$. The sets $A$ and $N(x)$ are disjoint.
Hence $N(v)\cup N(x)$ has at least $\lambda_{\max}+\delta$ vertices.
The pair $v,x$ together with the vertices outside that union is a
dominating set. Therefore $\delta+\gamma+\lambda_{\max}\le n+2$.
Separately, taking a vertex and all its nonneighbors shows
$\delta+\gamma\le n$.

[DeLaViña and Waller, Theorems 4 and 5](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v15i1r33/pdf/)
give $L_s+b\ge n+1$, and $L_s+b\ge n+2$ if $\lambda_{\max}\ge3$.
The Lean proof checks both needed bounds using their bipartite-block
construction. When $\lambda_{\max}\ge3$, start the first block with an
induced claw, then trim two leaves of the same color. Trim one at each
later block to pay for its connector.

The only remaining case is $\lambda_{\max}=2$ and $\delta+\gamma=n$.
Equality forces regularity and makes the nonneighbors of each vertex
independent: otherwise its dominating set can drop one of two adjacent
nonneighbors. Thus any edge dominates. Pick a vertex $v$ with two
nonadjacent neighbors $x,y$. Since $x$ has a nonneighbor and the graph
is regular, $v$ has a distinct nonneighbor $w$. Then $\{v,w\}$ and
$\{x,y\}$ give a bipartite induced set of order four. A dominating edge
gives $L_s\ge n-2$ by attaching each other vertex to an endpoint.
This supplies the required $n+2$.

## Lean replay

From a Lean 4.19.0 / Mathlib 4.19.0 project:

```sh
lake env bash /path/to/maths/graffiti-179/replay.sh
```

The script rebuilds the dependencies from this repository's #169 and
#177, then checks [Proof179.lean](Proof179.lean) with warnings as errors.
The axiom report for `Graffiti179.conjecture179` lists `propext`,
`Classical.choice`, and `Quot.sound` only.
