# Havel–Hakimi residue of hub–page graphs

This is a Lean-checked bridge from [Havel–Hakimi degree-list calculations](../autographforge-residue-phases/) to the [hub–page graph construction and its exact two-forcing number](../autographforge-forcing-twin-bound/). It does not yet certify unbounded gaps inside a particular graph class.

Every block has a pair of hubs and m independent pages adjacent to both hubs. H is the arbitrary graph on the hubs. Lean proves that the graph's degree multiset consists of every hub degree in H shifted by m, together with one degree 2 for every page. Because the Havel–Hakimi residue is invariant under permutations, the graph residue can be computed directly from these data.

With j+3 blocks and 4j+9 pages per block, Lean proves the following precise conditional statements:

| Degrees of H | Two-forcing number minus residue |
|---|---:|
| Two zeros, all others ones | 2j² + 8j + 7 |
| Two ones, all others twos | 2j² + 7j + 4 |

There is no graph-class condition in these statements. The separate verification that the intended chains realize the hub degree multisets and lie in the required graph classes is not part of this package.

**Replay:** use Lean 4.19.0 and a built Mathlib checkout at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Run `MATHLIB_DIR=/path/to/mathlib bash replay.sh`. The script builds the siblings and these modules into a fresh temporary directory and audits the named lemmas' axioms.
