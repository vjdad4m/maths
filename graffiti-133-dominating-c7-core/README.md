# Graffiti.pc #133: the dominating 7-cycle minimum-core branch

This is a **partial result** on the full conjecture. For a connected graph of radius at least four with no 4-cycle and no induced 9-vertex path, suppose a smallest connected dominating induced core is induced-P7-free and contains a dominating induced 7-cycle. Then the mean local independence number is at most four. The core may have any number of vertices. The proof handles the possible numbers of extra core vertices using weighted incidence bounds and the prior unrestricted two-control argument.

- [Lean statement and proof for the full branch](src/NestedCoreDominatingC7Branch133.lean)
- [Combined reduction at radius at least four](src/C7BranchResidualP5Core133.lean): after the 9-cycle and 7-cycle branches, a higher-mean graph must have a nested minimum P5-free core.
- [Radius bound for the nested P5-free case](src/C7BranchResidualRadius133.lean). The consequence at radius at least five is not claimed to be new: the stronger general induced-path theorem of [Erdős, Saks and Sós (1986)](https://real.mtak.hu/110576/1/1-s2.0-0095895686900286-main.pdf) gives an induced path on at least 2r−1 vertices for a connected graph of radius r.

[Strict modular replay](StrictReplay.log), standard Lean axioms only. With Lean and Mathlib 4.19.0, invoke `lake env bash /path/to/maths/graffiti-133-dominating-c7-core/replay.sh` from a prepared Mathlib checkout. This script rebuilds the public certificate dependencies.
