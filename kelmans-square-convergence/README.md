# Kelmans: convergence for disjoint square switches

Consider two alternate pairings of the opposite edges of each of a family of vertex-disjoint squares. A state uses one pairing per square and the same fixed edges. If each occupied switch edge has an alternate path in its state, then every initial state can reach the component partition of the union of all choices by repeatedly choosing a switch that joins two components. An even-degree supporting subgraph containing each switch edge suffices for the alternate-path premise; the whole state graph need not be even.

[Convergence theorem](src/RemoteSquareConvergence.lean) · [Even-degree support](src/RemoteSquareEvenScaffold.lean)

This is a sufficient condition for the switch-based approach to Kelmans. It does not assert that such a switch family exists in every graph or that arbitrary alternating circuits admit this convergence argument. The Hamiltonian specialization to cubic graphs partitioned into squares and a matching already follows from [Kotzig's compatible Euler-tour theorem](https://dml.cz/bitstream/handle/10338.dmlcz/136066/MathSlov_18-1968-1_8.pdf); [an explicit application is Lemma 2 here](https://pagesperso.g-scop.grenoble-inp.fr/~seboa/sebo_files/papers/lncs17ipcofund.pdf).

Compile with Lean/Mathlib 4.19.0 in the order in `modules.txt`, with warnings as errors. The exact checked sources use only standard axioms.
