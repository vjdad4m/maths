# Graffiti.pc #384b: closure of the seventeen-contact case

For a finite simple graph let T be the set of realized vertex triangle-incidence counts, including zero when it occurs. A 2-dominating set contains at least two neighbors of every vertex outside it. For connected graphs on n > 2 vertices, Graffiti.pc #384b asks whether γ₂ ≤ n − ⌈|T|/2⌉.

[Download the full source and replay archive](graff384b-joint17-sources.zip), including the pinned predecessor and strict verification instructions. Its SHA-256 is `9d48b8f73ae4711ccc7cdc60d781bbb7106f7fdd53eb3b478d9afb18bc310b3e`.

## Checked result

Assume n = 33, |T| = 31, and exactly 32 vertices have degree at least two. Fix a vertex e with distinct neighbors a,b, with N(e) = {a,b} and N(a) ∩ N(b) = {e}. Put A = {a,b} and W = V ∖ {e,a,b}. Let h count the vertices in W adjacent to at least one member of A.

If h ≥ 17, then γ₂ ≤ 17, the catalogue bound. Equivalently, every failure in this profile has h ≤ 16 for every such e. Earlier frozen work guarantees that a failure has at least one such e, exactly three degree-two vertices, and 29 vertices of degree at least three. The direct new theorem does not require separate input proofs of independence, connectedness, or the count of high vertices. [Direct catalogue theorem](JointEarRank.lean)

At h = 16, if the three degree-two vertices are independent and the inequality fails, every neighbor of either other degree-two vertex lies in X, the set of high vertices other than a,b. Here and below *high* means degree at least three. Thus all four of their incidences land in X, with multiplicity. A leaf in W is adjacent to a or b. It is the unique vertex of degree below two. In the case with an edge between two degree-two vertices, the previous release already shows that the other two form a pendant triangle in W. The h = 16 frontier and smaller h remain unresolved in general. [Independent case](JointEarRank.lean) · the weighted-repair predecessor bundled in the linked verification archive

## Joint choice of the ears

The predecessor reduces a hypothetical failure at h ≥ 17 to the case in which the anchors are high and all three ears are independent. Fix the two anchors and sample nine of the 27 vertices in X. For each sample s initially retain Xᶜ ∪ s, and promote each omitted high vertex that sees fewer than two retained vertices. Simultaneously remove every degree-two ear whose neighbors in X were all sampled. The distinguished ear e always qualifies. An eligible ear is safe because its exterior neighbors are retained and the ears are independent. A high vertex outside s cannot lose a retained neighbor to this operation: if it were adjacent to a removed ear, it would have belonged to s. [Pointwise construction and averaging](JointEarSample.lean)

Write F for the two ears other than e. Let c count their incidences outside X, and let z be one if the sole remaining vertex of W ∖ (X ∪ F) sees an anchor, zero otherwise. The checked inequality for a hypothetical failure with independent ears and high anchors is

```
629,850 h + 405,536 c + 629,850 (1 − z) ≤ 10,349,034.
```

At h = 17 the first term alone exceeds the right side by 358,416. At h = 16 the remaining allowance is 271,434. Either c ≥ 1 or z = 0 would exceed it. [Incidence inequality and its consequences](JointEarRank.lean)

The upper estimate ranks all 27 high vertices of X by their distinct triangle counts, starting at two. For each vertex it charges 629,850 per neighbor among the fixed anchors and 46,189 per neighbor among F. The resulting sum of degree-dependent deficiency counts and charges is at most 29,612,640. The dual prices were found by an external numerical calculation. A finite Lean proof verifies every required integer inequality for every rank and degree, including the capped-degree alternative. There is no solver or floating-point assumption in the proof. Lower estimates count all samples containing an ear's specified pool neighbors. An ear with zero, one, or two pool neighbors qualifies respectively in 4,686,825, 1,562,275, or 480,700 samples. The proof adds the two gains even when their neighbor sets overlap. [Rank table and fiber counts](JointEarSample.lean)

## A graph realizing the local profile

A connected graph on 33 vertices realizes h = 17, 31 triangle counts, 29 high vertices, 32 nonleaves, and dense five-clique centers at vertices 0 and 6. Its three degree-two vertices and neighbor sets are

| Vertex | Neighbors |
| --- | --- |
| 29 | 1, 4 |
| 30 | 2, 3 |
| 31 | 9, 10 |

Vertices 9 and 10 have exactly one common neighbor, vertex 31. All six displayed neighbors are distinct. The graph therefore rules out deriving a repeated ear neighbor from these local and numerical hypotheses alone. The set {1,2,3,4,9,10,14,15,18,19,32} 2-dominates the graph and has size 11. This graph satisfies the catalogue bound of 17. [Exact graph, connectivity, scores and 2-dominating set](JointEarWitness.lean)

A targeted search modified the anchor incidences of the 33-vertex graph in PortClique29. Lean verifies every stated property directly from the resulting adjacency masks. Search coverage supplies no step of the proof.

## Replay and source map

| File | Main dependency and output |
| --- | --- |
| JointEarSample.lean | Reuses Repair.omit_set, LowSample.anchor_samples, EarCredit.Pair.pair_fiber, and JointRank. Verifies the joint trial, its average, and the finite rank estimate. |
| JointEarRank.lean | Reuses Cover31.residual, Repair.maximal_diversity, PortRepair29.thin_degrees, and the frozen low-anchor and independence results in RankRepair29. Proves independent_budget, contact_cap, independent_sixteen, and exact_of_seventeen. |
| JointEarWitness.lean | Uses the previously checked edge-pair recurrence HighEar.pairs_insert and explicit rooted paths for the new graph. Proves connected and profile. |

The archived predecessor has SHA-256 `5f417c93ded057fcc6d3bafb4d38dbab5c3269adacd37fac1cdff1b3d3c949c1`. It carries the public thirty-high closure and three-four-cycle result. [Thirty-high closure](https://github.com/vjdad4m/maths/commit/fb935f0c968535bb210f00c8887072ccad900891) · [Three four-cycles](https://github.com/vjdad4m/maths/commit/c5a8c7c18be6dc644f2e1f61d687f560e69dccb1)

Extract the complete source package and enter graff384b-joint17. Supply Lean 4.19.0 at commit 6caaee842e94 and built Mathlib v4.19.0 at c44e0c8ee63ca166450922a373c7409c5d26b00b. To rebuild the entire proof chain, use

```bash
CROSSFOUR_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin \
CROSSFOUR_MATHLIB=/absolute/path/to/mathlib4-4.19.0 \
bash replay.sh --cold
```

The recorded entry point used `--checked-249 /absolute/path/to/Strict249.log /absolute/path/to/Strict166.log`. It verifies the archived 249-module baseline through the frozen predecessor's entry point, rebuilds Weighted29 and RankRepair29, and then compiles all three new modules. The cumulative chain covers 254 graph modules and 615 axiom reports. This run rebuilt five modules. Each new public theorem has an axiom check, warnings are errors, and the allowed axioms are propext, Classical.choice, and Quot.sound. The optional `--checked-base /absolute/path/to/Strict166.log` mode rebuilds the 88 modules following the 166-module baseline.

[Strict replay transcript](Strict254.log) · [New source hashes](NEW-SOURCES.sha256) · [Complete source manifest](SOURCES.sha256) · [Delivery manifest](DELIVERY.sha256)
