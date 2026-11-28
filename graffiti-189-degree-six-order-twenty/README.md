# Graffiti.pc #189: threshold-six equality case

At threshold d=6 and connectivity at least four, a nontraceable graph meeting the exact even-distance cap has at least **21 vertices**. This is one further order beyond the previous first-slack bound of 20. This does not solve #189 in general.

At order 20, the preceding floor proof forces a five-vertex omitted component and a longest path of length 14 (15 vertices). The component has at least four distinct pin positions, each in 1 through 13. By the terminal Ore splice, a gap shorter than six can only be between two pins held by one unique porter; two such short gaps cannot be adjacent because no vertex has three pins. Four pins in this interval force just two disjoint short gaps. The preceding two-per-block bound gives at most four pins, so all four belong exclusively to two porters. But at least three high-degree vertices in the component each require a pin, a contradiction.

Lean and Mathlib 4.19.0. Compile the earlier pin-budget and higher-degree first-slack packages (including WideWing189 and its prerequisite TerminalOreAdapter199), add their object directories to the Mathlib LEAN_PATH, and run replay.sh. The replay checks source hashes and builds with warnings as errors from a fresh object directory.
