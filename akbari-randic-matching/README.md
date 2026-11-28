# Akbari et al., Randić index vs. matching number

[Conjecture 9](https://arxiv.org/html/2402.12884v2#S5) asks for an absolute constant c > 0 such that the standard Randić index of a finite simple graph with matching number k is at least c times k to the power 2/3. Lean proves the whole statement in [Conjecture9.lean](Conjecture9.lean), with the explicit choice c = 2^(-1/3). The stronger proposed constant c = 1 is not proved here.

The Randić index is the sum over unordered edges uv of 1/sqrt(d(u)d(v)). Each matching of size k is encoded by an injection from k pairs of endpoints into the vertex set; the embedding requires an edge within each pair. The maximum permitted k is attained, including k = 0. Isolated vertices cause no difficulty because degrees are positive at edge endpoints.

Write m for the number of edges and R for the index. Two inequalities suffice:

* **m ≤ 2R².** Work with the 2m oriented edges. The sum of d(u)d(v) over these is at most its sum over all ordered vertex pairs, namely (2m)². Two applications of Cauchy–Schwarz, first to the geometric means and then to the means and their reciprocals, give the result.
* **k² ≤ mR.** Restrict to any k matching edges. The sum of their degree geometric means is at most half the sum of their endpoint degrees, hence at most m. The sum of the reciprocals is at most R. Apply Cauchy–Schwarz.

Together these give k² ≤ 2R³; taking cube roots yields the claimed constant.

**Replay:** Lean 4.19.0 and built Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Run `MATHLIB_DIR=/path/to/mathlib bash replay.sh`. All published theorems are checked with only standard Lean axioms.
