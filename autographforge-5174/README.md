# AutoGraphForge line 5174

**Proved.** In every regular graph with a numerical edge cover, the minimum edge-cover size is at most twice the minimum edge-domination size. Lean proves a sharper degree-excess bound and verifies that allowing degrees 1 through 3 already breaks the uncorrected inequality.

[Pinned catalogue statement](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L5174). The record was marked proposed in the pinned release; this is not a claim of historical priority.

## Degree-excess bound

For every finite simple graph of minimum degree at least k ≥ 1, Lean proves

```text
ρ ≤ 2γₑ + floor( Σᵥ max(0, deg(v) − k − 1) / k ).
```

Take the endpoint set S of a minimum edge-dominating set D. Every edge meets S and |S| ≤ 2|D|. Consequently every outside vertex has at least k neighbors in S. Each member v of S also has a neighbor inside S along its selected edge. At most deg(v)−1 of its neighbors lie outside. An incidence count bounds the Hall deficiency for matching the outside vertices into S by the displayed allowance. Complete the matched edges to an edge cover by adding an incident edge for each unused vertex of S and each unmatched outside vertex. The allowance vanishes whenever all degrees belong to {k,k+1}. On the claw the degrees are 1,1,1,3 and the values are ρ = 3 and γₑ = 1. With k = 1 the allowance is exactly one. `Spread.lean` certifies the failure beyond degree spread one and equality in the corrected bound.

The regular case is a consequence of Caro, Davila and Pepper’s inequality δα ≤ Δν. In a positive-degree regular graph it gives α ≤ ν. Gallai’s edge cover identity gives ρ = n−ν ≤ n−α. The endpoints of D are a vertex cover, so n−α ≤ 2γₑ. `Regular.lean` gives an independent proof and the degree correction using the checked Hall deficiency construction from row 1553. Historical priority for the correction was not established. [Caro, Davila and Pepper, *New results relating independence and matchings*](https://arxiv.org/abs/1909.09093) · [Yannakakis and Gavril, *Edge Dominating Sets in Graphs*](https://doi.org/10.1137/0138030)

## Replay

With Lean and a built Mathlib v4.19.0, use `MATHLIB_DIR=/path/to/mathlib4 bash replay.sh`. [Strict replay](Replay.log).
