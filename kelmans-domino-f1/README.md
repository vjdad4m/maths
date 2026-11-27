# Prescribed-vertex deletion in the cyclic-4 Kelmans class

**This is a conditional reduction, not a solution of Kelmans's conjecture.** Suppose every finite simple cyclically 4-edge-connected, 3-vertex-connected cubic graph of order divisible by six has a $P_3$-factor. Then for every graph in the same connectivity class of order congruent to four modulo six, deleting **any prescribed vertex** leaves a graph with a $P_3$-factor.

The Lean theorem is [`cyclic4_factor_implies_f1`](src/DominoF1.lean). The order-four case is checked directly. For larger graphs the cut assumption rules out triangles, and the proof uses two [handle extensions](../kelmans-handle) followed by [prescribed adjacent-pair deletion](../kelmans-affine-t2).

## Construction

Let $x$ be the vertex to delete. Choose neighbors $a,d$ of $x$ and let $b,w$ be the two other neighbors of $a$, with $d\ne w$. Subdivide $xd$ and $aw$ and join the subdivision vertices $Y,A'$ by a new edge. Next subdivide $xa$ and $YA'$ by vertices $q,r$ and join $q$ to $r$. Both steps use disjoint edge pairs and preserve the connectivity class. The resulting graph has order two modulo six, so adjacent-pair deletion applies to the edge $xY$.

After deleting $x,Y$, relabel $A'$ as the old vertex $a$, and the original vertex $a$ as an added vertex $p$. The three added vertices induce the path $p-q-r$. They touch the old vertices only through $pa,pb,ra$ in the relabelled graph. Edges between old vertices are edges of $G-x$, except that $ab$ is missing.

If the three added vertices form a tile, remove it. Otherwise their tiles together use precisely three old vertices: $a,b$ and a third vertex $z$ adjacent to one of them. Restore $ab$, replace those tiles by one $P_3$ on $a,b,z$, and keep the other tiles. The [repair lemma](src/DominoRepair.lean) checks all possible residual tile patterns.

## Scope and replay

This proves the cyclic-4 version of the vertex-deletion strengthening denoted (f1) in [Kelmans's Theorem 3.1](https://arxiv.org/abs/0910.2766). It does not establish the ordinary conjecture, and the construction does not assert preservation of an arbitrary girth threshold.

From a Lean 4.19.0 project with the Mathlib 4.19.0 build cache:

    lake env bash /path/to/maths/kelmans-domino-f1/replay.sh
