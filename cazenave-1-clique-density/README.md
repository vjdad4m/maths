# Cazenave Conjecture 1: large cliques and dense graphs

This is a partial result for [Cazenave's Conjecture 1](https://arxiv.org/abs/2611.03879v1).
Write n and m for order and size. Let t be the lower eigenvalue of a pair of
ordered nonzero orthogonal adjacency eigenvectors. These proofs use the
conventional Randić index over unordered edges.

* `clique_complement_spectral`: a clique of size k with r vertices outside
  gives t+1 ≤ q whenever r≤q and kr≤4q(q−r). The optimal q in this
  statement is (r+sqrt(r²+kr))/2.
* `clique_density_randic`: if also q(n−1)≤m, the desired inequality
  R≥t+1 follows.
* `near_clique_randic`: in particular, R≥t+1 if 5r≤k (at least 5/6
  of the vertices form a clique).
* `very_dense_randic`: with no clique hypothesis, R≥t+1 if the minimum
  degree is at least d and 2(n−1)(n−1−d)≤nd. In particular, minimum
  degree at least 2(n−1)/3 suffices.

For the clique bound, choose a nonzero linear combination of the given
eigenvectors with zero sum on the clique. Its Rayleigh quotient is at
least t. The clique block contributes the negative of its squared norm
on the clique. Centering the cross coefficients by subtracting 1/2 and
using Cauchy–Schwarz gives the cross-term bound
(2 cross)² ≤ kr times the product of the squared norms on the two blocks.
The outside block contributes at most r−1 times its squared norm.
This yields the displayed test for q. For the density bound, impose
zero sum on the whole graph, so the complement gives the negative
energy minus the squared norm. Bounding complement energy below by
minus its maximum degree times the squared norm proves
t+1 ≤ maximum complement degree. In both applications we use
R ≥ m/(n−1).

The matrix-to-eigenpair step for t=λ₂ is a standard application of the
real symmetric spectral theorem in prose, not a dependency of these
Lean files. No full resolution or novelty is claimed.

Replay with Lean 4.19.0 and Mathlib commit
c44e0c8ee63ca166450922a373c7409c5d26b00b using `lake env bash /absolute/path/to/this/package/replay.sh` from the
pinned Mathlib checkout. It reuses support modules from the [triangle-free package](../cazenave-1-triangle-free/). Only the ordinary axioms propext, Classical.choice,
and Quot.sound occur in the checked declarations.

## Four-fifths improvement

`four_fifths_clique_randic` extends the near-clique threshold to 4r≤k:
a clique containing at least four-fifths of the vertices suffices. The
proof splits on the number e of clique-to-outside edges. For e≤k²/24 it
uses a stronger cross-term estimate from e; for e≥k²/24 it uses the
extra edges to improve the Randić lower bound. The eigenpair formulation
and spectral-bridge limitation are the same as above.
