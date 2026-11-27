# Graffiti.pc #199 at connectivity three

In a minimum-order nontraceable graph of vertex connectivity three satisfying the catalogue bound, assume the degree-three vertices are independent. Choose a separating triple, one of its ports `r`, and the connected ordinary shore `X` opposite its isolated vertex `z`. Let `M` consist of the vertices of `X` missed by `r`. **At most one connected component of the induced graph on `M` has an edge.** This holds for every ordering of every separating triple. The baseline supplies at least three vertices of `M`, a spanning path of the deletion of `z`, and the independent terminal quartet. [Integrated theorem](src/CatalogueMissComponents.lean)

An ordinary contact of a component is a vertex in `X` adjacent to `r` and to at least one member of that component. Call a component uniform if it is a clique and every ordinary contact sees all its members.

* If the component with an edge is uniform, it consists of a pair `u,v`. Both endpoints have degree at least four. They have the same unique cubic neighbor, an ordinary contact whose neighborhood is exactly `{r,u,v}`. Every ordinary contact of any other missed component also touches the pair. [Uniform pair theorem](src/SplitEdgeClosed.lean) · [Cubic contact theorem](src/CubicContactGeometry.lean) · [Unique cubic neighbor](src/CubicPairReduction.lean)
* If a component is nonclique, the ordinary contact sets of **all** distinct missed components are disjoint. Inside any component, fix an ordinary contact `p` and retain the vertices missed by `p`. Each resulting component is a clique with uniform attachments to neighbors of `p` inside the original component. Their attachment sets are disjoint. [Nested clique and contact theorems](src/NestedMissStructure.lean)
* Each ordinary contact meets at most two missed components. The unordered pairs realized by contacts meeting two components are empty, have a common component, or are exactly the three pairs of three components. This also covers the case in which every missed vertex is isolated. [Two-contact bound](src/DoubleAttachment.lean) · [Pair classification](src/AttachmentShape.lean)

## Why the uniform edge with a cubic member closes

A vertex with no cubic neighbor can be deleted while preserving three-connectivity under the surviving-edge condition. Minimality supplies a spanning path of that deletion. In a nontraceable graph, each neighbor of the deleted vertex must have two distinct path neighbors outside its closed neighborhood. Two vertices of a uniform missed clique can differ in their outside neighborhoods only at the other ports `a,b`. Together these facts bound the clique's order by two. For a two-vertex uniform clique containing a cubic vertex `s`, its mate `t` sees both `a,b`, while `s` sees neither. [Safe deletion](src/SafeOmission.lean) · [Clique size and port pattern](src/UniformCliqueSize.lean)

The members share precisely two ordinary contacts. The induced-six-tree bound and the minimum degree force at most one further missed vertex `w`. The three-miss theorem provides this vertex. It sees at least one of `a,b`. Take a shortest ordinary path from `s` to `w`. It avoids `t`, since every other ordinary neighbor of `t` is a neighbor of `s`. Prepending `t` gives a route between contacts of the two outer ports containing all three misses. Only its first interior contact can neighbor `s`, so the other shared contact is available for the previously checked spanning-path splice. This rules out this configuration at every graph order. [Third miss](src/SplitThirdMiss.lean) · [Chordless connector](src/TwinConnector.lean) · [Splice](src/SplitRoute.lean) · [Minimum-order exclusion](src/SplitEdgeClosed.lean)

The exact integrated symbol is `Graffiti199Depleted.Catalogue.Incomplete.catalogue_minimum_miss_component_profile`. Its minimum-order premise quantifies over all smaller connected graphs on at least two vertices meeting their own catalogue bound. Its other hypotheses are order at least five, exact vertex connectivity three, the catalogue induced-tree inequality, nontraceability, and independent cubic vertices. The contact-shape theorem only needs the graph-level `SingletonCut` data. The theorem gives no upper bound on the number of isolated misses. The all-isolated case, a unique nonuniform component, and a uniform pair with the specified cubic contact remain for further analysis, subject to the checked restrictions. The full connectivity-three case and unrestricted #199 remain unresolved here.

## A graph that tests the stronger clique claim

The proof gives an explicit 11-vertex graph. In order, the four groups induce a singleton, a triangle, a four-clique, and a three-vertex path. All consecutive groups are joined completely. There are no further intergroup edges. The graph has connectivity exactly three, tree number at most five, one cubic vertex, the surviving-edge property for every deletion of at most three vertices, and a Hamiltonian path. Every port in the displayed cut misses precisely the final path. Its two ends are nonadjacent and belong to the same actual miss component. This supplies a limitation on graph-level clique claims. [Witness and invariant certificates](src/NoncliqueExample.lean)

## Sources and replay

The header and first 177 source records reproduce the frozen exact-two package's manifest byte for byte. Its SHA-256 is `27f3d7de23453791f23559387ef18b1cd8a0d683225e9f702d1b747c57a19e3a`. The archive includes all 199 Lean sources. The 22 new modules have their direct imports recorded separately. [Ordered source hashes](Manifest.tsv) · [New module imports](NewModules.tsv)

The proof uses the archived #199 surviving-edge theorem, omission flanks, induced-tree orderings, private-component definitions, root-four clique lemmas, chordless connectors, and reserved-edge splice. The #189 prescribed-endpoint Ore theorem occurs in the inherited source closure. The new graph does not come with its required degree-sum bound on each missing edge of the route graph. The new proof uses the spare common contact of the paired vertices.

From the extracted directory, use a compiled Mathlib v4.19.0 checkout at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` with Lean 4.19.0.

```sh
GRAFF199_MATHLIB=/path/to/mathlib4 GRAFF199_LEAN_BIN=/path/to/lean-4.19.0-linux/bin \
  bash replay.sh > StrictReplay.log 2>&1
python3 audit.py
```

The runner checks every source digest and compiles in manifest order into a fresh temporary project object directory with warnings as errors. The audit checks the frozen prefix, replay order, full source inventory, proof tokens and final axiom lists. The integrated theorem, split-edge exclusion, and attachment classification each print exactly `[propext, Classical.choice, Quot.sound]`. [Strict replay](StrictReplay.log) · [Axiom and source audit](FinalAudit.log)

[Complete pinned Lean sources](proof-sources.tar.gz). Extract the archive and use its replay script.
