# The six-dimensional bad science matrix optimum

This addresses the exact dimension-six optimization in [Steinerberger's
Some Open Problems, §30](https://faculty.washington.edu/steinerb/openproblems.pdf)
and [Bad Science Matrices, §2.6](https://arxiv.org/html/2402.03205v2).
Steinerberger gives the candidate lower bound `(2 + sqrt(3))/2`. Here is a
matching upper bound with a Lean-checked finite table. The full real-valued
argument below is **not** formalized end to end. No novelty or priority claim
is made.

## Proof

Let X be the 32 sign vectors with first coordinate +1, representatives
modulo antipodes. For each x in X choose a row i attaining the greatest
absolute row evaluation, and choose a sign s(x) making its evaluation
nonnegative. Let S_i be the resulting set assigned to row i, k_i its size,
and w_i the sum of s(x)x over S_i. If every row has norm one, Cauchy–Schwarz
bounds the unnormalized objective by the sum of the six norms of the w_i.

For a row with k assigned points, each coordinate of w is between -k and
k and congruent to k modulo two. Sort the absolute coordinates into u.
Signed coordinate permutations preserve the multiset of absolute dot
products with X: they induce permutations of the antipodal classes.
Writing P_k(u) for the sum of the k largest absolute dot products, we have
`||u||^2 = ||w||^2 = w · sum s(x)x <= P_k(u)`.
Thus a necessary condition on u is testable without enumerating subsets.

For k = 0, …, 11 the kernel-checked table in Certificate.lean bounds
the squared norm by
`[0, 6, 20, 38, 64, 86, 116, 150, 192, 214, 244, 278]`.
It enumerates just sorted coordinate vectors with the correct parity and
range; a vector is discarded if its squared norm exceeds P_k.
The insertion routine keeps the k largest entries in descending order.

For k >= 12 use orthogonality of the coordinate columns of X:
the sum of (w · x)^2 over X is 32 ||w||^2. Consequently
`||w||^2 <= sum_{x in S_i} |w · x| <= sqrt(32 k) ||w||`,
so `||w|| <= sqrt(32 k)`; the zero case is immediate.

In all cases `||w|| <= L(k)` where
`L(k) = 16 - 8 sqrt(3) + (2 sqrt(3) - 2) k`.
For k = 4 and 8 this follows from the exact table bounds. At the other
small values the table comparison is verified by
`chord_arithmetic`: the rational line `(1464k + 2143)/1000` dominates
the square root of the table and lies below L(k) since
`1.732 <= sqrt(3) <= 1.732125`. For k >= 12 the same rational line dominates
`sqrt(32k)`: subtracting `32000000k` from `(1464k + 2143)^2` and substituting
`k = 12 + u` leaves strictly positive coefficients.

Sum L(k) over the six rows and divide by 32. Since the sizes sum to 32,
the resulting average is at most `(2 + sqrt(3))/2`.

For attainment, split X into two groups of size eight on the side
x_2 = +1 by x_3, and four groups of size four on the side x_2 = -1
by (x_3,x_4), with coordinates numbered from one. Each row takes the fixed
signs on one group, divided by the square root of their number, and zero
elsewhere. The two larger groups contribute at least sqrt(3) per point
and the four smaller groups at least 2 per point, achieving the upper
bound. The integer evaluation counts are also checked in Lean.

## Replay

With Lean 4.19.0, run `lean Certificate.lean`. No Mathlib is needed.
The finite checks use the Lean kernel, not native evaluation or admitted
propositions. The paper's prior lower bound and the later dimension-five
result are not claimed as findings here.
