# Cyclic-four Kelmans: avoiding two incident edges

Assume the P₃-factor conjecture for finite simple cubic 3-vertex-connected, cyclically 4-edge-connected graphs of order divisible by six. In **the same class**, a factor can avoid any two specified distinct edges incident to one vertex. Equivalently, at any chosen vertex one can prescribe its edge as a leaf of its three-vertex path. This is a conditional strengthening, not a proof of the starting conjecture.

The proof uses a cyclically 4-edge-connected test graph made from six copies of the graph with two adjacent vertices removed. Two marked, disjoint ring edges can be avoided by the [disjoint-edge theorem](../kelmans-handle). Counting vertices modulo three forces a cell where one can insert both deleted vertices back and complete the packing using the prescribed edge.

- **Lean:** [RoutedLeafFactor.lean](src/RoutedLeafFactor.lean), theorem `cyclic4_factor_avoids_adjacent`
- **Replay:** in a Lean 4.19.0 project with Mathlib 4.19.0, run `lake env bash /path/to/maths/kelmans-adjacent-avoidance/replay.sh`.
