# Graffiti.pc #384b at sixteen exterior anchor contacts

**Result.** Let $G$ be a finite simple graph on 33 vertices. Suppose exactly 32 vertices have degree at least two and there are 31 distinct values of the number of triangles through a vertex. Let $e$ have exactly two neighbors $a,b$, with $N(a) ∩ N(b) = {e}$. Let $h$ count the vertices outside $e,a,b$ adjacent to at least one of $a,b$. If $h ≥ 16$ and some two degree-two vertices are adjacent, $G$ has a 2-dominating set of size at most 17. Equivalently, any counterexample with adjacent degree-two vertices has $h ≤ 15$ at every such ear. [Main theorem](PendantBound.lean#L135)

The exact pendant-triangle theorem also works without the thinness assumption. It assumes $N(u)={v,z}$, $N(v)={u,z}$, with $u,v,z$ exterior to $e,a,b$, and gives the catalogue bound at $h ≥ 16$. Both theorems cover disconnected graphs under their stated hypotheses. The case $h=16$ with three pairwise nonadjacent degree-two vertices and the general conjecture remain outside this branch. [Pendant theorem](PendantBound.lean#L38)

## Proof

In a hypothetical failure under these quotas there are 29 vertices of degree at least three, with distinct triangle counts all at least two. Pick 26 of these vertices away from the anchors $a,b$ and the triangle attachment $z$. Call the resulting pool $X$. Keep every vertex outside $X$ except $e,v$. Each of those two omissions already has two kept neighbors, and neither has a neighbor in $X$. The four vertices of the exterior outside $X$ include $u,v$, which have no anchor adjacency. Thus at least 14 vertices in $X$ have a fixed neighbor among $a,b$.

Choose nine of the 26 pool vertices uniformly and keep them. Together with the five vertices already kept this costs 14. Also keep each omitted pool vertex that has fewer than two kept neighbors. There are 3,124,550 equally likely samples. At rank $r$ starting from zero, the local triangle count is at least $r+2$, so the degree is at least the smallest $d$ with `choose(d,2) ≥ r+2`. The standard bad-sample bound for this vertex is `choose(25-d,9) + d*choose(25-d,8)`. With a fixed anchor neighbor the bound improves to `choose(26-d,9)`. The calculation uses lower degree bounds capped at eight.

Summing the larger of the first bound and the second plus 377,910 over the 26 ranks gives 17,538,628. Subtracting the charge for 14 credited vertices leaves at most 12,247,888 deficiency occurrences, which is 250,312 below four times the sample count. Some sample therefore has at most three deficiencies. Repairing it costs at most 17 in total. [Rank table and fixed-omission argument](PendantSample.lean) · [Averaging and graph reduction](PendantBound.lean)

The catalogue problem is due to Ermelinda DeLaVina’s Graffiti.pc. The argument uses the repository’s published 29-high reduction, triangle-count rank lemmas, finite-sample deficiency bound, fixed-neighbor fiber bound, and the earlier weighted package’s low-anchor and pendant-triangle reductions. This extension introduces the 26-vertex sample with two protected omissions and applies its new rank budget. It uses no theorem from the separate independent-ear lane. [Original catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Published diversity-31 reduction](https://github.com/vjdad4m/maths/tree/fb935f0c968535bb210f00c8887072ccad900891/graffiti-384b-rich-degree31) · [Published four-cycle reduction](https://github.com/vjdad4m/maths/tree/c5a8c7c18be6dc644f2e1f61d687f560e69dccb1/graffiti-384b-three-squares)

## Replay

The two new modules are here. The replay script reads the exact 251-module predecessor from the [seventeen-contact archive](../graffiti-384b-joint17/graff384b-joint17-sources.zip). Lean is 4.19.0, commit `6caaee842e94`. Mathlib is v4.19.0, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. In the shared workspace, run the recorded entry point from this directory.

```bash
bash replay.sh --checked-251 ../graff384b-weighted29/Strict251.log
```

The recorded run rebuilt both new modules with warnings as errors in a fresh directory after verifying the predecessor manifest, transcript, extension audit and five directly reused compiled objects. It checked each of the five new theorem axiom reports against `propext`, `Classical.choice`, and `Quot.sound`. [Strict transcript](Strict253.log) · [Source hashes](NEW-SOURCES.sha256)

For a standalone source build, enter this directory and run the following command with the indicated toolchain and built Mathlib available. The recorded run reused the checked predecessor. A fresh build of all 251 predecessor modules was not repeated for this extension.

```bash
CROSSFOUR_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin \
CROSSFOUR_MATHLIB=/absolute/path/to/mathlib4-4.19.0 \
bash replay.sh --cold
```
