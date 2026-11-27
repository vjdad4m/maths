# Graffiti.pc #199: restrictions on the cubic vertices

The formal hypotheses are order at least ten,
`Catalogue.ConnectivityAtLeast G 3`, `Catalogue.treeNumber G ≤ 5`,
and `CrossingBetweenSurvivingEdges G`. The last is the archived cut
condition that deleting at most three vertices cannot separate two
surviving edges.

- `adjacent_cubic_no_common_neighbor` proves that an edge between two
  degree-three vertices has four distinct outside neighbors. A common
  neighbor would bound the outside neighborhood by three. Its exterior
  must then be independent by the cut law, and minimum degree three
  makes this exterior a source of five leaves of an induced star.
- `no_induced_two_cubic_edges` excludes an induced two-edge matching on
  the degree-three vertices. Delete the shared boundary if it has at
  most two vertices and use two private ports and the shortest-connector
  lemma to obtain an induced six-vertex path. If at least three ports
  are shared, delete the at most two private ports. Shared ports cannot
  have an edge leaving the union of the pair neighborhoods, so the
  deletion is a cut.
- `cubic_edges_in_same_component` gives the conclusion directly in the
  graph induced by the degree-three vertices. All its edges belong to
  one connected component. This excludes the earlier two-pair pattern
  using just its low vertices. Triangle halves, higher degree at the
  ports, a four-block cover and an independence bound are unnecessary.

The explicit obstruction is a 12-clique with a cubic three-vertex path
attached at five distinct clique vertices. Its end vertices each have
two clique neighbors and its middle vertex has one. It has connectivity
three, the archived cut property, induced-tree number at most five, no
independent six-set, and a Hamiltonian path. Every cubic edge has another
cubic vertex in its outside neighborhood. Also, every cubic edge
contains the middle vertex, whose three neighbors are mutually
nonadjacent, so there is no `FullPair` at all. This example tests the
implication from the listed graph and cut hypotheses.

The cut hypothesis is the exact `CrossingBetweenSurvivingEdges`
interface of the [archived integration proof](https://github.com/vjdad4m/maths/blob/main/graffiti-199-four-block-integration/src/RemainingCut.lean).
The new proof uses the [published shortest connector](https://github.com/vjdad4m/maths/blob/main/graffiti-199-canonical-four-block-obstruction/src/ShortestConnector.lean)
and generalizes the shared-port trapping argument to cubic edges with
arbitrary ports. The remaining minimum-counterexample work concerns the
single edge-containing cubic component, or cases with no such component.
The full conjecture remains open.

## Replay

Use Lean 4.19.0 and Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. From the repository
root, set `GRAFF199_MATHLIB` to the local Mathlib checkout and run:

    bash graffiti-199-cubic-matching/replay.sh --from-source "$PWD"

The script checks source hashes and compiles with warnings as errors.
