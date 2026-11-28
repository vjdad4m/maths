# Graffiti.pc #384b with six triangle contacts

Let G be a finite simple graph with 29 distinct vertex triangle counts, 29 vertices of degree at least two, and 27 vertices of degree at least three. The two degree-two vertices are the ears. Their neighbors are the anchors. A triangle contact is a high vertex outside the anchor set on a triangle with an anchor. If there are exactly six contacts, then **γ₂(G) ≤ |V(G)| − 15**. The theorem permits disconnected graphs and any order. Neighbor sets of the ears need no additional hypotheses. In this profile, a failure must have between seven and fourteen contacts, inclusive. The general conjecture remains open. [Graph theorem and corollary](SixComplete.lean) · [Ermelinda DeLaViña’s catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Catalogue data, entry 384b](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json)

## Two ways to repair the cut

A protected cut pins vertices on two disjoint shores. Every pinned vertex has two neighbors on the opposite shore. When the cut contains both ears, maximum-cut completion gives the required two-domination bound.

If one anchor sees both neighbors of the other ear, the two ears and four anchors give a cut with at most one deficient anchor. It has a second triangle. A triangle that reaches another pinned vertex can repair the gap immediately. When both triangle partners lie in the pool of high nonanchors, the triangle offers two routes of opposite parity to either partner. An edge to another anchor or an additional triangle contact gives a return of length two, three or four, of the parity required by the pinned shores. A four-edge return can end at the original anchor. If both partners are private, the previously checked three-pin theorem applies. This proves the fork case for **every** contact count in this profile. [Alternating returns](ThreadCut.lean) · [Pool-triangle lemma](TriangleReturn.lean) · [Unconditional fork theorem](ForkClosure.lean) · [Reused three-pin theorem](prior/ScoreFreePatch.lean)

A separate repair applies when the deficient anchor has exactly two triangles and a free triangle whose two partners can be moved. Among the high vertices, triangle scores are distinct and at least two. A cubic vertex has at most three triangles, so at most one unpinned cubic can remain. If it misses one partner, that partner can be moved safely in a maximum cut with a cardinality tie-break. Only its neighbors need degree at least four to absorb the move. If the cubic sees both partners, it supplies a four-cycle instead. This argument allows other pool vertices to be pinned already. [Localized exchange and score-two repair](CubicMove.lean) · [Predecessor exchange](prior/Recolor34_384b.lean)

## Finite certificate and transfer

A failure supplies four distinct high anchors, each of score at least two, with one of score at least thirteen. The published triangle-free-nonleaf theorem implies that each ear lies on a triangle, so its two anchors are adjacent. Label the major anchor first and order the six contacts with its neighbors first. Every triangle at any anchor is contained in these twelve labeled vertices. There are seven possibilities for the number of contacts adjacent to the major anchor. [Construction of the labeling](SixLayout.lean) · [Exact transfer, including the nonleaf-zero theorem](SixTransfer.lean) · [Published nonleaf-zero proof](https://github.com/vjdad4m/maths/commit/6c3123cd92e5b51d023054ebe2f7c88ca58ce871)

A decision tree branches on the 45 possible edges among the ten high labels. Each leaf checks one of four conditions in Lean. An upper completion can have too few triangles at an anchor. A lower completion can contain a protected cut or a fork. The last kind supplies a one-gap cut and a free triangle in the lower completion, with the deficient anchor’s score bounded by two in the upper completion. The soundness theorem proves each certificate valid for every intermediate edge assignment. The seven trees have 7,529 nodes in total, including 22 leaves using the score-two repair. The graph transfer then establishes the result for the original graph, including arbitrary exterior edges and vertices. [Soundness of the checker](SixModel.lean) · [Complete seven-case application](SixComplete.lean)

The local search and the encoder are included for reproducibility. The Lean proofs validate the resulting tree data with kernel reduction. The checked search produced the same certificate byte for byte using these commands.

```sh
c++ -std=c++20 -O3 -Wall -Wextra -Werror certificate.cpp -o certificate
./certificate > reproduced.tree
cmp certificate.tree reproduced.tree
```

Running `python3 -B encode.py` on the supplied `certificate.tree` reproduces the seven `SixPack` Lean sources.

## Replay

From the extracted source directory in the shared workspace, supply the absolute workspace root to the checked entry point. It verifies all 388 predecessor object hashes and all 404 Lean source hashes before rebuilding the 16 new modules. The pinned toolchains are Lean 4.19.0 at `6caaee842e94` and Mathlib 4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```sh
w=/absolute/path/to/predecessor-checkout
SIX_LEAN_BIN="$w/graff384b-codex/.deps/lean-4.19.0-linux/bin" \
SIX_MATHLIB="$w/graff384b-codex/.deps/mathlib4" \
python3 -B replay.py --checked "$w"
```

For a full source rebuild using matching Lean and Mathlib installations, set the same environment variables to those installations and run `python3 -B replay.py --cold`. The strict replay uses warnings as errors and audits each new theorem’s printed axioms against `propext`, `Classical.choice` and `Quot.sound`. [Replay script](replay.py) · [Strict extracted-package transcript](StrictSix.log)

The three-pin predecessor source archive used here has SHA-256 `4d9c9e95215b1d9fa689af17b5ab5e848296eb1bf8033f6caf546aa9d71804bf`. The second dependency is the published zero-nonleaf module and its Hall and parity reductions. The proof uses the frozen positive-triangle and high-score lemmas, the five-contact lower cutoff and maximum-cut completion from the shared research repository. The published nonleaf-zero dependency includes the Mathlib Hall theorem under its upstream attribution. The full cold predecessor rebuild is available through the entry point. This release used hash-checked predecessor objects for the independent replay. [Imported sources and hashes](PREDECESSORS.sha256) · [Existing five-contact reductions](https://github.com/vjdad4m/maths/tree/6c3123cd92e5b51d023054ebe2f7c88ca58ce871/graffiti-384b-five-triangle-contacts)

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
