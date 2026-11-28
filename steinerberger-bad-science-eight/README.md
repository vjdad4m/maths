# Dimension-eight matrix bound: diagnostic

Steinerberger's arXiv:2402.03205v2, §2.8, gives the lower bound 2.
For a winner cell of size k among the 128 antipodal representatives, let q
be the squared norm of the sum of oriented sign vectors. Then q is at most
128k by Parseval, at most k times the sum of the absolute coordinates,
and at most the sum of the k largest projections onto that signed sum.
We may sort the absolute coordinates by sign-cube symmetry.

For k=1 through 38 the exact C++ search enumerates sorted parity-compatible
vectors with max coordinate at most k, q greater than floor((17k+48)^2/100),
and both Parseval and maximum-projection necessary bounds. All 1,016,256
vectors violate the remaining top-k projection bound. Also, for every k
one common threshold works in the equivalent one-sided budget bound
k*t + sum (abs(projection)-t)_+. The replay log prints all successful
tested thresholds. This eliminates sorting in a prospective Lean checker.

For k>=39, sqrt(128k) <= (17k+48)/10 by direct quadratic expansion
around k=39. The same upper bound is immediate at k=0. The eight cell
sizes sum to 128, so summing the affine bound yields 2 after dividing by
128. For attainment use the eight rows matching the first three free
bits with four entries of absolute value 1/2. Witness8.lean checks the
integer part of the construction. The upper-bound search and reduction
are not yet checked in Lean. This is not a claim of novelty.

Four cutoffs suffice across all sizes in this screen: 32 for sizes 1–6,
38 for 7–11, 45 for 12–16, and 52 for 17–38. Each lies in the interval
printed by the exact search for every size in its range.

Replay the finite construction with `lean Witness8.lean` on Lean 4.19.0.
To replay the independent integer screen, run
`g++ -std=c++20 -O3 row.cpp -o row && ./row`.
