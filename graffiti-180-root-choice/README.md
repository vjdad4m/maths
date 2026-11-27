# An exact root-deletion formula for Graffiti.pc 180

Let a connected graph H be obtained from a connected graph G of order at least three by adding a root r with neighbor set N in G. For a graph K and a set of eligible vertices S, let W(K,S) be the maximum number of eligible leaves of a spanning tree. This package uses the published Lean representations `ear G N` and `lift U e`, where U is a set of old eligible vertices and e records whether the new root is eligible.

If r has at least two neighbors, then

```
W(H, U with r eligible) =
  max( W(H, U),
       1 + max_{x∈N} W(G, U ∖ {x}) ).
```

Marking r increases the optimum by one exactly when at least one neighbor x satisfies

```
W(G, U ∖ {x}) = W(H, U).
```

The theorem `apex_score` covers both Boolean eligibility settings. The theorem `apex_gain_iff` gives the equality criterion. These statements apply at every odd-cycle transversal number.

The threshold formulation `star_or_deletion` works for any nonempty N. A target t is attained precisely when a tree containing every root edge attains t, or a neighbor x satisfies `t ≤ W(G,U ∖ {x}) + e`, with e interpreted as zero or one. If an optimal tree makes r internal, the published full-star exchange preserves every eligible leaf that it previously counted. If r is a leaf with neighbor x, suppressing r gives a connected old graph. In a tree of order at least three, x and r cannot both be leaves. The counted old leaves therefore transfer to the old marking with x excluded. In the other direction, the published leaf-attachment bound realizes the lower threshold in H.

This gives an unrestricted spanning-tree alternative for the rank-three example in the companion package. It also leaves a smaller graph in the branch where the root becomes a leaf. The transfer does not assert that deleting the root preserves its original distance parity classes. Applying either alternative to every remaining rooted marking is the open part of #180.

All four theorems are in namespace `Minimal180.HigherRank` in `RootChoice180.lean`. The direct imports are `MinimalVertex180`, `MiddleCertificate180`, `FirstForm180`, and `StarExchange180`. The transitive project imports are bundled at exact public Git blob IDs, with their repository paths in `published-blobs.txt`. [Published repository at the pinned revision](https://github.com/vjdad4m/maths/tree/a5807be3c5e58d04f3a972d3fe2bc58a96499447)

From the extracted folder, run

```sh
LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin \
MATHLIB_DIR=/absolute/path/to/mathlib4 bash graffiti-180-root-choice/verify.sh
```

The required Mathlib revision is `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The verifier rebuilds the source closure with warnings as errors, replays the new declarations, and audits all four axiom reports.

The clean replay recompiled all 49 published imports and accepted all 10 new declarations. Each of the four printed reports lists exactly `propext`, `Classical.choice`, and `Quot.sound`.
