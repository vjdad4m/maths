# Erdős Problem #324: collisions for an infinite family of quartics

The [catalogue problem](https://www.erdosproblems.com/324) asks whether an integer-coefficient polynomial can have distinct sums on all pairs of distinct nonnegative inputs. This package does **not** resolve that question. It excludes the candidates
`f(x) = x⁴ + (c k²)x²` for each integer `1 ≤ c ≤ 32` and `k ≥ 1`.

A pair-sum search supplied explicit collisions for the 32 base coefficients. Lean checks every witness and proves the identity
`f_(c k²)(kx) = k⁴ f_c(x)`, so all the dilated candidates are excluded as well. The search program is not in the proof's trusted base. The collision at `c = 1` uses `(37,50)` and `(22,53)`.

The known degree-at-most-three obstruction is due to [Dubickas and Novikas](https://doi.org/10.1002/mana.202000334). We do not claim novelty for these individual witness calculations, nor for the general problem.

Replay with Lean 4.19.0, without Mathlib:
```sh
lean -j1 -DElab.async=false -DwarningAsError=true QuarticCollisions.lean
```
The final theorems use only `propext` and `Quot.sound`.
