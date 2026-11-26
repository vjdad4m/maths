# Graffiti.pc #169: even-distance counts and spanning-tree leaves

For a finite simple connected graph of order (n\ge 2), let (L) be its
maximum number of leaves among spanning trees. Let (E(r)) count vertices
at even shortest-path distance from (r), including (r). Then
[
L\ge 1+\max_r E(r)-\min_r E(r).
]

The [catalogue statement](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf)
does not explicitly exclude the singleton. With the degree-one definition
of a leaf, its left-hand side is zero and its right-hand side is one.
If its sole vertex is counted as a leaf, it satisfies the inequality
with equality. The Lean file proves the nontrivial case and explicitly
checks the degree-one convention at order one.

## Proof

An [earlier written proof, dated November 24, 2026](https://github.com/f8bsd9yqgp-maker/Solved-conjectures-/blob/03b6cd13bac0975fb554633e47a30c64cbf6a1bf/proofs/graffiti-pc-169/README.md), uses the same parity degree-sum argument with a breadth-first spanning tree. This repository gives an independent Lean formalization. No discovery priority is claimed.

Fix a root (r), and keep the edges whose endpoints have different
distance parities from (r). This gives a connected spanning subgraph:
every nonroot vertex can follow a shortest path to a neighbor one
distance level closer. Any spanning tree (T) of this subgraph has
the even-distance and odd-distance classes as independent sets.

For either of these classes (A), the edges incident to its members are
disjoint as sets of edges, since no edge has both ends in (A).
The members of (A) have degree at least two in (T), except for leaves,
which have degree one. Thus (2|A|-L\le |E(T)|=n-1). Applying this
to both classes gives ((n+1-L)/2\le E(r)\le(n-1+L)/2).
Taking the difference between the largest and smallest root counts gives
the claim.

## Lean

[Proof169.lean](Proof169.lean) is standalone apart from Mathlib.
It reuses the leaf and distance-parity definitions from this repository's
[#177](../graffiti-177/Short177.lean) and [#318](../graffiti-318/Proof318.lean).
From a Lean 4.19.0 / Mathlib 4.19.0 project run:

```sh
lake env lean -DwarningAsError=true /path/to/maths/graffiti-169/Proof169.lean
```

The axiom report for `Graffiti169.conjecture169` lists only
`propext`, `Classical.choice`, and `Quot.sound`.
