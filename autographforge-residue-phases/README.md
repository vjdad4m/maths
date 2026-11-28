# Havel–Hakimi residue: the hub and terminal phases

These reusable Lean lemmas use the same Havel–Hakimi implementation as [Graffiti.pc #324](../graffiti-324/Proof324.lean).

- `residue_perm`: the residue is unchanged by permuting the input list.
- `hubs_go_first` and `hub_phase_residue`: if there are h hub entries, each at least h + 2, and all other entries are at most 2, then the algorithm peels every hub before removing a page. At each step it decrements every other hub and uses the remaining budget on the highest page degrees. The resulting page list has the original page count and its residue equals the original residue.
- `residue_even_ones`: a terminal list with 2p ones and z zeros has residue p + z.

[ResiduePhases.lean](ResiduePhases.lean) covers the two structural stages needed after the [general two-forcing formula](../autographforge-forcing-twin-bound/). The counting step is proved below; the graph-class lifts remain separate.

## Exact page counts and the two chain degree lists

[PageCounts.lean](PageCounts.lean) tracks the counts of twos, ones and zeros in descending order. One step decrements twos before ones. If the initial mass exceeds total spending by twice the largest individual budget, this rule never spends on a zero. During the hub stage the total page expenditure is the initial hub degree sum minus h(h−1), where h is the initial number of hubs. Combining the count with the terminal phase gives the residue for both parametric degree lists:

| List, with k ≥ 3 and t = 4k − 3 | Havel–Hakimi residue |
|---|---:|
| Fan chain: 2k−2 hubs of degree t+1, two of degree t, and kt pages of degree 2 | 2k² − k − 1 |
| Book chain: 2k−2 hubs of degree t+2, two of degree t+1, and kt pages of degree 2 | 2k² − 1 |

Lean uses the additive parameter j = k−3. This proves the exact residue at the degree-list level. A graph-level proof must still identify each constructed graph's degree list and check its graph class for all k.

## Replay

Use Lean 4.19.0 and built Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash autographforge-residue-phases/replay.sh
```

Replay builds from source with warnings as errors and checks that the exported theorems use only standard Lean axioms.
