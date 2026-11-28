# One-low-degree circumference and the normalized separated-double branch

Lean checks the general finite one-low-degree circumference bound for graphs
connected after deleting fewer than two vertices, with minimum degree two
and at most one vertex below m≥2: a cycle has length at least min(n,2m).
The proof implements the interval-chain and two-track argument of [L. Pósa
(1963), Theorem 3](https://real.mtak.hu/201453/1/cut_MATKUTINT_8_3_1963_pp355_-_361.pdf)
using a longest path with two high ends; it avoids edge-maximal supergraphs.

The branch theorem rules out a normalized nontraceable #189 graph when
κ=d−2≥10 and a high omitted root has two separated pins on the chosen
longest path and a neighbor off the path. The prior shore theorem's
circumference premise is proved internally. This is not unrestricted #189.

Replay with Lean/Mathlib 4.19 and earlier #189 theorem objects on LEAN_PATH.

[Main Lean theorem](PosaOneLow189.lean) · [Verified replay](VERIFIED.log).
See the [preceding shore reduction](../graffiti-189-odd-minimum-cycle/) for
the definition of the separated-double branch and the earlier dependency chain.
