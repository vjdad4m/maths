# Cazenave §7, Conjecture 6(i)

For every finite connected simple graph with at least two vertices and (m) edges, the usual Randić index satisfies (R^2ge (m+1)/2).

This is a Lean formalization of the exact inequality printed in [Cazenave's paper, §7](https://arxiv.org/html/2611.03879v1#S7), **not a new resolution**. The stronger bound (Rge (1+sqrt{1+8m})/4) already follows from the general Randić lower bound of [Elphick–Wocjan](https://arxiv.org/abs/1508.07950) at exponent (-1/2) and [Stanley's 1987 spectral upper bound](https://math.mit.edu/~rstan/pubs/pubfiles/71.pdf). Indeed, (Rge m/lambda_1) and (lambda_1le(sqrt{1+8m}-1)/2); squaring the resulting bound gives at least ((m+1)/2) when (mge 1).

The Lean proof is independent of those spectral estimates. It applies Cauchy–Schwarz to the oriented edges and bounds the resulting sum of degree products by the sum over all off-diagonal vertex pairs. A third Cauchy–Schwarz inequality and (|V|le m+1) give the claimed constant. The unordered-edge theorem is `Cazenave.randic_sq_lower_edges`.

Replay: in Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b` (Lean 4.19.0), run `lake env lean -DwarningAsError=true /absolute/path/to/RandicSixI.lean`. The final line prints the axiom dependencies.
