# Defect amplification for Kelmans's P₃-packing conjecture

**This does not prove or disprove Kelmans's conjecture.** It proves that two apparently weaker universal guarantees would each imply the full conjecture.

A P₃-packing is a set of vertex-disjoint three-vertex paths; the paths need not be induced. Its defect is the number of uncovered vertices. On finite simple cubic 3-vertex-connected graphs whose order is divisible by six, Lean verifies the equivalence of:

1. Every graph has a perfect P₃-packing (a P₃-factor).
2. Every graph has a P₃-packing of defect at most $h$, for any fixed integer $h\ge 0$. In particular, the guarantee of at most three uncovered vertices suffices.
3. As the order increases, every graph has a packing with a uniformly vanishing defect fraction. Precisely: for each positive integer $s$, all sufficiently large graphs have a packing of defect at most their order divided by $s$.

[Lean statements and proofs](src/NearPerfectEquivalence.lean): bounded_equiv, vanishing_equiv, universal_iff_starter. The theorem replica_family_gap states the quantitative obstruction directly.

## Amplification

Suppose there is a counterexample $G$ of order $n$. Delete one vertex of $G$ to make a cell with three ports, its former neighbors, and substitute this cell for every vertex of a cubic 3-connected base on $k$ vertices. The joining edges form a matching. A packing either does not use a joining edge, giving port widths $(0,0)$, or uses it in a path, giving widths $(1,2)$ or $(2,1)$.

Each fully covered cell exports a total width congruent to two modulo three. Total width two would allow the deleted vertex to cap its exported fragments and give a factor of $G$, so a fully covered cell must have widths $2,2,1$. Score widths $0,1,2$ by $1,2,0$, respectively. Every joining edge contributes two points, so the total score is $3k$. A cell with $m$ uncovered vertices contributes at most $2+2m$: this follows from the width pattern for $m=0$, the residue for $m=1$, and the trivial bound of six for $m\ge2$. Thus any packing with defect $d$ has $3k\le2k+2d$, or $d\ge k/2$.

Lean checks that the constructed graph is again simple, cubic and 3-connected. Using arbitrarily large valid base graphs produces graphs of order $k(n-1)$, each of which has defect fraction at least $1/[2(n-1)]$ in every packing. This rules out both proposed weaker guarantees if a counterexample exists.

## Relation to prior work

The rooted vertex sum, its repetition, and the use of crossing paths in perfect factors are from [Kelmans, *Packing 3-Vertex Paths in Cubic 3-Connected Graphs*, §§2.1–2.4 and §3.8](https://arxiv.org/abs/0910.2766). This package formalizes the construction and the quantitative score argument for partial packings. It makes no priority claim.

## Replay

Use a Lean 4.19.0 project with Mathlib 4.19.0 and its build cache:

    lake env bash /path/to/maths/kelmans-defect/replay.sh

The script builds the source dependencies in a temporary directory and checks the headline theorems with warnings as errors. The proof uses Lean's standard axioms only.
