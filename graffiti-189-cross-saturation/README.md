# Graffiti.pc #189: degree-four case for all 2-connected graphs

**Lean proves Graffiti.pc #189 for all 2-connected graphs whose second-smallest degree is four.** More explicitly, assuming at most five vertices (including the base vertex) at even graph distance from any vertex, and at most one vertex of degree less than four, every finite 2-connected simple graph has a Hamiltonian path. There is no graph-order limit. [Final Lean theorem](src/DegreeFourTwoConnected189.lean).

The proof uses the previously checked order-at-most-17 theorem and the structural near-connectivity and distance-three arguments. If a minimum cut has two vertices, the cut leaves exactly two components; it remains to prove the nearby-cut cases, which is the new ingredient below.

For a two-vertex cut separating two sides, call a vertex a port when it is adjacent to a cut vertex. A common port is adjacent to both cut vertices. Under the second-smallest-degree threshold four, if one side has a common port and the other has at least three distinct ports, **the graph has a spanning path**. This is an order-independent consequence of the catalogue even-distance constraint. [Exact Lean theorem](src/NearForeignSaturation189.lean).

A second theorem proves traceability when the two cut vertices are at graph distance at most two, under the same degree threshold and the explicit two-side and connectivity hypotheses. No limit on graph order is assumed. [Exact Lean theorem](src/DistanceTwoCut189.lean).

Two intermediate bounds allow a general positive even-distance budget (d): a cut endpoint with (d) ports on the same side forces order at most (3d+2), and a common port facing (d) distinct opposite ports forces order at most (4d+1) (at most (4d) for a nonadjacent cut). The near-saturation argument takes advantage of the one unused even-distance slot in the three-port case, bringing it into the checked order-17 range. The hypotheses for each cut and side are explicit in the Lean statements.

This is not a proof of the full conjecture: cut-vertex graphs and other degree regimes are not covered here. For cut-vertex graphs, see the written result in [Easwar and Johari, Theorem 5.11](https://arxiv.org/html/2609.11719v1), which this package does not formalize. [Strict replay](StrictReplay.log) uses standard axioms only. Rebuild with Lean and Mathlib v4.19.0: `lake env bash /path/to/maths/graffiti-189-cross-saturation/replay.sh`.
