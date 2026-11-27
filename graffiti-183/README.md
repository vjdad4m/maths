# Graffiti.pc #183: spanning-tree leaves, bipartite order, and square radius

For a finite simple connected graph \(G\) with at least two vertices,

$$
L_s(G)+b(G)\ \ge\ \Delta(G^2)+2\operatorname{rad}(G^2).
$$

Here \(L_s\) is the maximum number of leaves in a spanning tree, \(b\) is the maximum order of an induced bipartite subgraph, and \(G^2\) joins vertices at original distance one or two. This is the [exact catalogue statement](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf).

- [Lean theorem](src/Proof183.lean)
- [Written proof](PROOF.md)

The metric side is at most \(n+2\); the spanning-tree and bipartite side is at least \(n+1\) by [DeLaViña and Waller](https://doi.org/10.37236/757). A failure would therefore have equality on the left and hit \(n+2\) on the right. The metric equality singles out two vertices \(v,w\), at distance three, such that no other vertex is more than two steps from \(v\).

Maximize a connected induced bipartite subgraph containing \(v,w\). Equality in the leaf bound forces outside vertices that prevent two vertices of the block from being removed at once. Those outside vertices turn the block into a larger odd cycle. The possible neighborhoods on that cycle then propagate around it, forcing a common neighbor of \(v,w\), a contradiction.

## Replay

Use a Lean 4.19.0 project with Mathlib 4.19.0 and its build cache:

    lake env bash /path/to/maths/graffiti-183/replay.sh

The script compiles the source dependencies in a temporary directory and checks the exact catalogue theorem with warnings as errors.
