# Graffiti.pc #384b: a universal one-vertex gap

**Partial result.** Let n be the graph order, and t the number of distinct vertex triangle counts. The conjectured upper bound on the minimum size of a 2-dominating set is n − ⌈t/2⌉. Lean proves the upper bound n − ⌈t/2⌉ + 1 for every finite simple graph. It proves the exact conjectured bound for connected graphs of order greater than two with at most four distinct triangle counts, and under the high-degree-count hypothesis in `exact_of_high`.

See [Proof384b.lean](src/Proof384b.lean), especially `within_one` and `exact_of_at_most_four`. This does not settle the general conjecture.

In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-384b-partial/replay.sh`.
