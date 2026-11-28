# Exact bad science matrix optimum in dimension seven

[Steinerberger's original paper, §2.7](https://arxiv.org/html/2402.03205v2#S2.SS7)
gives the candidate value `(6 + sqrt(3))/4`. The Lean theorem
`BadScienceSeven.Formal.exact_full_cube_optimum` in `Main7.lean` proves
both attainment and global optimality over all unit-row real 7 × 7 matrices.
The objective is the maximum absolute row evaluation, averaged over all
128 sign inputs.

Unlike the [earlier C++ screen](../steinerberger-bad-science-seven/), the Lean
proof needs no sorting of the absolute projections. A uniform threshold
26 (cell sizes below 14) or 30 (sizes 14 through 23) gives a sufficient
integer upper bound. The finite certificate splits by the size of the cell,
and the real-valued reduction proves that every winner cell satisfies the
hypotheses of the certificate. Parseval handles sizes at least 24 without
enumeration.

With Lean 4.19.0 and the pinned Mathlib revision, run:

```sh
lake update
lake exe cache get
bash replay.sh
```

The replay uses sequential finite checks to limit peak memory. The axiom
audit for the final theorem lists only `propext`, `Classical.choice`
and `Quot.sound`.
