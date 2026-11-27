# Graffiti.pc #133: induced seven-vertex paths and new bounded-radius cases

**Partial result for #133.** Lean proves that a finite connected graph with no four-cycle (induced or not) and average local independence strictly above three contains an induced path on seven vertices. There is no exclusion of five-, six-, or seven-cycles in this statement.

This proves the conjectured unrounded bound for radius at most three and average at most four, and for radius at most two and average at most five. The source also proves the corresponding bounds when the floor of the average is used. The general conjecture remains open.

See [HexFlattened133.lean](src/HexFlattened133.lean), including `P7_of_strict_mean_three` and the four radius theorems. The proof reduces to a six- or seven-cycle in a graph where every vertex has local independence at least two. A structural counting argument on vertices around those cycles rules out a strict mean above three in the absence of the induced path.

In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-133-induced-seven/replay.sh`.
