# Seven-dimensional bad science matrices

[Steinerberger's §2.7](https://arxiv.org/html/2402.03205v2#S2.SS7)
gives the candidate lower bound `(6 + sqrt(3))/4`. This folder records a
matching computational upper-bound argument. **Only the attaining
construction's integer checks are Lean-checked so far.** The general
upper-bound argument and its finite screen are not checked in Lean yet.

Use the winner-cell decomposition from the
[six-dimensional Lean proof](../steinerberger-bad-science-six-complete/).
Now the antipodal half-cube has 64 points; the seven cell sizes sum to 64.
For a cell of cardinality k the squared norm q of the oriented sum satisfies
`q <= P_k`, the sum of the k largest absolute projections on its sorted
absolute coordinates. Each such coordinate is at most k and congruent to
k modulo two.

For k from 1 through 23, `row.cpp` checks every sorted parity-compatible
coordinate vector with squared norm above the proposed bound. A vector
is rejected when the directly calculated `P_k` is smaller than q. The
bounds are 256 at k=8, 768 at k=16, and otherwise
`floor((1464k + 4286)^2 / 1000000)`. At k=0 the sum is zero. This is exact
integer arithmetic; no floating-point estimate is used by the verifier.

The resulting norm bound is at most
`L(k) = 32 - 16 sqrt(3) + (2 sqrt(3) - 2) k` throughout: this is exact at
k=8 and k=16, and for other k below 24 the line dominates the rational
proxy `(1464k+4286)/1000`, as in dimension six. For k>=24 use Parseval to
bound the norm by `sqrt(64k)`, which the rational proxy dominates (substitute
`k=24+u` and expand the square). Summing L over the seven cells and
dividing by 64 gives `(6 + sqrt(3))/4`.

For attainment, in the antipodal half-cube partition by two free sign bits.
Keep one of the four resulting size-16 groups intact and bisect the three
others by a third bit. The corresponding rows use their group's fixed
coordinates, normalized to unit length. `Witness.lean` checks the integer
row norms, chosen evaluations and cell counts for exactly this construction.

## Replay

```sh
lean Witness.lean
g++ -std=c++20 -O3 row.cpp -o row
./row
```

The first command uses Lean 4.19.0. The upper-bound screen is an ordinary
C++ computation, not a Lean theorem.
