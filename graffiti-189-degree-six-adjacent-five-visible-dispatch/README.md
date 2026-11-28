# Graffiti.pc #189: five visible sites in the order-16 adjacent singleton split

For degree six and the even-distance cap of seven, suppose an adjacent
two-vertex separator leaves a singleton and a 13-vertex component, and
exactly five vertices of the large component are adjacent to the separator.
Lean proves a spanning path except for the case with three dark vertices
at distance two from both separator vertices and minimum dark internal
degree below four. In particular, the two-balanced case is complete,
including the case with a deep vertex.

Use Lean/Mathlib 4.19.0. Replay the dense three-balanced checkpoint
first, then the two-deep and residual dispatcher, in the order recorded
in each subdirectory. See their READMEs for prior objects on LEAN_PATH.
This package is not the full order-16 adjacent proof or full conjecture.
