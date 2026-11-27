# Cazenave Conjecture 1: cyclic triangle-free case

This is a **partial result**, not a resolution of Cazenave's full Conjecture 1
([preprint, §7](https://arxiv.org/abs/2611.03879v1)).
For a connected finite simple triangle-free graph containing a cycle, the Lean
theorem `CazenaveOne.triangleFree_orthogonal_not_acyclic` proves
`t + 1 ≤ randic G` from a nonzero orthogonal pair of adjacency eigenvectors
for ordered eigenvalues `t ≤ L`.  The Randić index in the theorem is the
conventional sum of inverse square roots over unordered edges.  In ordinary
mathematics the real symmetric spectral theorem supplies this pair with
`t = λ₂` and `L = λ₁`; this certificate does not import or formalize that
matrix-to-eigenpair step.  Every nonbipartite triangle-free graph contains a
cycle.  The preprint already proves the separate bipartite case.

## Proof outline

1. Sum the degrees on the neighborhood of each vertex. Its neighbors are
   independent, so every edge contributes at most once. After weighting by
   the degree and summing, the sum of degree products over edges is at most
   the square of the edge count. Two Cauchy–Schwarz applications give
   `R ≥ √m`.
2. For a positive eigenvalue `t`, restrict a sign-changing eigenvector to
   each sign class. At a maximum of the restricted nonnegative function, the
   iterated eigenvalue sub-equation and the same independent-neighborhood
   count give `t² ≤ m₊` and `t² ≤ m₋`, the two internal edge counts.
   The eigenvector for the lower of any two ordered orthogonal eigenvectors
   changes sign: positivity propagates from any nonnegative eigenfunction
   by connectivity, and a maximum ratio of the two eigenfunctions then
   contradicts orthogonality.
3. Connectivity ensures `m₊ + m₋ + 1 ≤ m`; when both counts are at most
   three and a cycle exists, there must be at least two outside edges:
   a unique crossing would be a bridge and put the entire cycle in a class
   of at most three edges. These bounds and elementary inequalities give
   `t+1 ≤ √m`.

This is an independent combinatorial derivation of a known-bound consequence:
Cazenave's `R ≥ m/λ₁` and the Lin–Ning–Wu triangle-free spectral bound
`λ₁² + λ₂² ≤ m` already imply the claim for `λ₂ ≥ 1`. For `λ₂ < 1`,
Cazenave's degree-independent bound `R ≥ √(n−1)` handles every order
at least five; nonbipartite triangle-free graphs have that order. See also
[Nikiforov's proof of the spectral bound](https://arxiv.org/abs/2104.12171).
No priority or full-solution claim is made.

`CliqueBound.lean` contains a separate numerical implication: **assuming**
the Bollobás–Nikiforov bound and the Randić lower bounds, the conjectured
inequality follows when `λ₂ ≥ ω−1` or order `n ≥ ω²+1`. This file
does not establish or import those graph hypotheses.

## Replay

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. From the pinned Mathlib checkout,
run `lake env bash /absolute/path/to/this/package/replay.sh`. The file order is Core, Nodal, Perron, MainLarge,
Small, CliqueBound. The proof files use neither locally added axioms nor
unverified declarations.
