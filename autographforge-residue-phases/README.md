# Havel–Hakimi residue: the hub and terminal phases

These reusable Lean lemmas use the same Havel–Hakimi implementation as [Graffiti.pc #324](../graffiti-324/Proof324.lean).

- `residue_perm`: the residue is unchanged by permuting the input list.
- `hubs_go_first` and `hub_phase_residue`: if there are h hub entries, each at least h + 2, and all other entries are at most 2, then the algorithm peels every hub before removing a page. At each step it decrements every other hub and uses the remaining budget on the highest page degrees. The resulting page list has the original page count and its residue equals the original residue.
- `residue_even_ones`: a terminal list with 2p ones and z zeros has residue p + z.

[ResiduePhases.lean](ResiduePhases.lean) covers the two structural stages needed after the [general two-forcing formula](../autographforge-forcing-twin-bound/). It does **not** yet count the surviving ones and zeros for the entire counterexample family, or certify the graph classes in general.

## Replay

Use Lean 4.19.0 and built Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash autographforge-residue-phases/replay.sh
```

Replay builds from source with warnings as errors and checks that the five exported theorems use only standard Lean axioms.
