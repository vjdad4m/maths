# Exact bad science matrix optimum in dimension six

[Stefan Steinerberger's *Bad Science Matrices*, §2.6](https://arxiv.org/html/2402.03205v2#S2.SS6)
gives `(2 + sqrt(3)) / 2` as a lower bound. This package proves
the matching upper bound and attainment over the real numbers.

The final theorem is `BadScienceSix.Formal.exact_full_cube_optimum` in
`Main.lean`. It quantifies over all real 6 × 6 matrices with unit Euclidean
row norms and uses the maximum absolute row evaluation, averaged over all
64 sign inputs. The theorem asserts both that the value is attained and
that it bounds every matrix.

- `Certificate.lean`: preliminary integer certificate and chord arithmetic.
- `Base.lean`: orthogonality, Cauchy–Schwarz and the finite threshold-budget
  certificate; only the certificate bits are evaluated by decision procedures.
- `Main.lean`: coordinate symmetries, soundness of the threshold argument,
  optimal upper bound, explicit maximizing matrix, and transfer to the full cube.

See the [written argument in the earlier package](../steinerberger-bad-science-six/).
No novelty or priority claim is made.

## Replay

Use Lean 4.19.0 and the pinned Mathlib revision:

```sh
lake update
lake exe cache get
lake build
```

The final `#print axioms` audit should list only `propext`, `Classical.choice`,
and `Quot.sound`. No native decision procedure or admitted proof is used.
