# Graffiti.pc #189: all eligible unique-common distance-two cuts

Lean proves that the degree-five Graffiti.pc #189 hypotheses force a Hamiltonian path when two vertices at distance two have exactly one common neighbor, their deletion leaves exactly two components, and at most one other vertex is adjacent to neither endpoint. This last condition is the degree-sum test from [Easwar and Johari](https://arxiv.org/html/2609.11719v1#S3). The proof constructs the path directly in the original graph. It covers the possible low-degree vertex on either side of the cut and does not assume the general edge-addition lemma.

- [Exact traceability theorem](DegreeFiveUniquePortClosureFull189.lean) and [low vertex in the common-neighbor component](DegreeFiveUniquePortLowCommon189.lean).
- [Terminal-preserving Ore closure](TerminalOreClosure189.lean) and [a two-terminal path through a clique with one outlier](TerminalOutlier189.lean).
- [Separate large-order reduction](DegreeFiveFourForeign189.lean): under the same cut shape and unique common neighbor, but **without** assuming the degree-sum test, order at least 17 forces at most three vertices on the opposite component adjacent to a cut endpoint.

The general conjecture and the degree-five cuts outside the test remain open. The new declarations passed strict Lean 4.19 replay with standard axioms only. Build the public [degree-five cuts](../graffiti-189-degree-five-cuts/) and [prior closure-test package](../graffiti-189-closure-test/) first. Then compile the five modules in the order listed in `modules.txt`, with the prerequisite objects and pinned Mathlib on the Lean search path.
