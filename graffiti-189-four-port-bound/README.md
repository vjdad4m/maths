# Graffiti.pc #189: the four-port singleton order bound

**Partial result.** Under the degree-four even-distance hypotheses used in #189, let a degree-two vertex have exactly four distinct outside neighbors of its two neighbors, excluding the degree-two vertex and its two neighbors and let every other vertex have degree at least four. Lean proves that the graph has at most twelve vertices. This is a structural reduction, not an assertion that all the remaining finite orders have a Hamiltonian path.

See [ExcludeOrderThirteen.lean](src/ExcludeOrderThirteen.lean), theorem `order_le_twelve`. The proof first bounds the order by thirteen, then rules out equality by counting how many vertices can occur at distance two from the ports.

In a Lean and Mathlib 4.19.0 project, run `lake env bash /path/to/maths/graffiti-189-four-port-bound/replay.sh`.
