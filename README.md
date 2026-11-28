# maths: Problem index

[Source catalogues and numbering](SOURCES.md) · [Graffiti.pc](#graffitipc) · [Graffiti³](#graffiti-3-index) · [AutoGraphForge](#autographforge) · [Extended proof trails](PROOF-TRAILS.md)

## Find a result to reuse

Start with the structure of the new problem. The **check before reuse** column is where a transfer can fail. The status tables below tell you what was actually settled.

| If your problem involves… | Start with this result | Check before reuse |
|---|---|---|
| **Hall matching, clique covers, rainbow domination** | [AutoGraphForge 1121](autographforge-1121/README.md): `match_outside` converts crossing-degree bounds into a matching that saturates the outside of a chosen set. The match produces a partition into edges and singletons. For [vertex covers](autographforge-rainbow-vertex-cover/), it suffices to exclude adjacent uncolored vertices. | Need a positive threshold: at least that many crossing neighbors outside-to-inside and at most that many inside-to-outside. The rainbow application uses singleton labels. |
| **Independent sets, spanning-tree leaves** | [Graffiti.pc #177](graffiti-177/Short177.lean): marked-leaf construction; [tree equality](graffiti-177/TreeEquality.lean) gives test cases for sharpness. | Transfer the construction, not the numerical bound, if the new hypothesis is missing the relevant degree or bipartite-subgraph parameter. |
| **Hamiltonian paths across small separators** | [#189 linkage and endpoint splicing](graffiti-189-hall-linkage/) · [#199 labelled splice adapters](graffiti-199-overlap-adapters/). First build paths in the sides with specified endpoints, then join them. | Need compatible endpoints and disjoint vertex sets. Under distance constraints, adding an edge can change shortest-path parity. Neither package settles its full conjecture. |
| **Longest induced paths, forbidden cycles, radius** | [#133 mean-four theorem](graffiti-133-full-four/README.md) · [Induced eight-vertex path](graffiti-133-induced-eight/README.md). Reuse the path extension and chord exclusions. | Check which cycle lengths are forbidden, whether cycles are ordinary or induced, and the exact mean and radius thresholds. |
| **Two-domination, cuts, repairing a sample** | [#384b discounted repairs](graffiti-384b-discounted-repairs/README.md): use a cut among deficient vertices to add fewer repairs than one per vertex. | Bound the size of the initial sample and its residual deficit separately. The repair lemma is general; the catalogue bound is not settled. |
| **Degree sequences and Havel–Hakimi residue** | [#324](graffiti-324/Proof324.lean): formal residue computation and the elimination argument. | A degree-sequence inequality does not by itself supply the graph structure used by the main theorem. |
| **Cubic graphs, perfect matchings, edge and clique covers** | [AutoGraphForge 1160](autographforge-1160/README.md): perfect-matching criterion on triangle-free positive-degree regular graphs. [Cubic odd-block witness](autographforge-cubic-odd-blocks/README.md): one hub attached to three odd lobes, with exact invariant values. [Two implication transfers](autographforge-cubic-odd-implications/). | The equivalence needs triangle-freeness. The witness is connected but has bridges; it cannot attack a bridgeless claim. Several catalogue rows are equivalent. |
| **Cographs, trees, degree-sequence invariants** | [Cograph-tree star profile](autographforge-cograph-trees/): a proper join with no triangles or four-cycles is forced to be a star; seven invariants then count its leaves. | A cograph tree must be connected, acyclic, and have at least two vertices. A disconnected cograph forest need not obey the same formulas. |
| **Burning, radius, and domination on paths or cycles** | [AutoGraphForge 1130](autographforge-1130/README.md): exact cycle calculations; [cycle transfers](autographforge-cycle-implications/README.md) show how to substitute shared values into different comparisons. | Check connectedness and optional-invariant conventions; distinguish an explicit new certificate from a witness already implicit upstream. |
| **Zero or two-forcing on trees** | [Star witness](autographforge-star/StarCone.lean) · [star transfers](autographforge-star-implications/README.md): forcing values and a simple non-claw-free bipartite example. | A high-degree star cannot test a subcubic or claw-free claim. Check the precise forcing process. |
| **Forcing and vertices with identical neighbors** | [Reusable Lean lemmas](autographforge-forcing-twin-bound/): seed all but k vertices per twin block; the requirements add over disjoint blocks. A graph of n paired hubs and m private pages per pair has exact two-forcing number n(m−2) for m≥3. See [842](autographforge-842/), [2535](autographforge-2535/) and [676](autographforge-676/). | Hub edges may vary, but the page neighborhoods must stay identical within each block. For Havel–Hakimi, see the [hub-first and terminal-phase lemmas](autographforge-residue-phases/). The exact [page counts](autographforge-residue-phases/PageCounts.lean) give the two chain degree-list formulas. The [graph-residue bridge](autographforge-parametric-chains/) gives explicit connected planar bipartite and connected chordal K₄-free families with unbounded forcing–residue gaps. |
| **Spectral radius and adjacency rank** | [Cazenave §7, 6(iv), rank half](cazenave-6iv-rank/): Lean proof and equality case. | Check which rank and index the new statement uses; do not conflate the rank half and the edge-count half. |
| **Prescribed terminals in a path factor** | [Kelmans one-handle reduction](kelmans-one-handle/README.md) · [two-edge avoidance](kelmans-handle/README.md) · [cap validity](kelmans-theta-faithful-cap-validity/). | Check residue class of the order, connectivity, and what the boundary gadget actually preserves. The general Kelmans conjecture remains open. |

## Kelmans

| Problem | Resolution status | References |
|---|---|---|
| Kelmans P₃-factor conjecture | Open; bounded and sublinear defect equivalences proved (also within cyclic-4 at fixed girth) | [General](kelmans-defect/README.md) · [Cyclic-4/Fixed girth](kelmans-defect-cyclic/README.md) · [Full proof trail](PROOF-TRAILS.md#kelmans-p3) |

## Spectral graph theory

| Problem | Resolution status | References |
|---|---|---|
| Cazenave §7, 6(i) | Formalized (follows from prior work) | [Lean proof](cazenave-6i/) |
| Cazenave §7, 6(iv) rank | Proved; equality iff K₂ | [Lean proof and written argument](cazenave-6iv-rank/) |
| Cazenave §7, 1 | Open; cyclic triangle-free eigenpair theorem formalized | [Lean partial](cazenave-1-triangle-free/) · [bounded local triangle counts](cazenave-1-bounded-triangles/) · [large cliques and high minimum degree](cazenave-1-clique-density/) |

## Graffiti.pc

| Problem | Resolution status | References |
|---|---|---|
| Graffiti.pc #40 | Unresolved here |  |
| Graffiti.pc #61 | Unresolved here |  |
| Graffiti.pc #76 | Disproved | [Lean](graffiti-76/Verify76Exact.lean) · [Write-up](graffiti-76/README.md) |
| Graffiti.pc #108 | Disproved | [Lean](graffiti-108/Counterexample108.lean) · [Write-up](graffiti-108/README.md) |
| Graffiti.pc #111 | Proved | [Lean](graffiti-111/Proof111.lean) |
| Graffiti.pc #133 | Open in general; real mean ≤ 4 and floored mean ≤ 4 proved | [Full mean-four range](graffiti-133-full-four/README.md) · [Earlier cases](graffiti-133-induced-eight/README.md) · [Full proof trail](PROOF-TRAILS.md#graffiti-pc-133) |
| Graffiti.pc #137 | Proved (order ≥ 2); disproved (singleton) | [Lean](graffiti-137/Proof137.lean) · [Earlier nontrivial-case argument](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/blob/main/README.md#finding-3--conjecture-137-is-a-theorem-in-four-lines) |
| Graffiti.pc #138 | Disproved | [Lean](graffiti-138/Verify138.lean) |
| Graffiti.pc #154 | Disproved | [Lean](graffiti-154/Counterexample154.lean) |
| Graffiti.pc #157 | Proved | [Lean](graffiti-157/Formal157.lean) · [Write-up](graffiti-157/README.md) |
| Graffiti.pc #161 | Proved | [Lean](graffiti-161/Proof161.lean) · [Write-up](graffiti-161/README.md) |
| Graffiti.pc #166 | Disproved | [Lean](graffiti-166/Counterexample166.lean) |
| Graffiti.pc #169 | Proved (order ≥ 2); singleton depends on leaf convention | [Lean](graffiti-169/Proof169.lean) · [Write-up](graffiti-169/README.md) · [Earlier written proof](https://github.com/f8bsd9yqgp-maker/Solved-conjectures-/blob/03b6cd13bac0975fb554633e47a30c64cbf6a1bf/proofs/graffiti-pc-169/README.md) |
| Graffiti.pc #177 | Proved | [Lean](graffiti-177/Proof177.lean) · [Shorter Lean proof](graffiti-177/Short177.lean) · [Tree equality](graffiti-177/TreeEquality.lean) |
| Graffiti.pc #179 | Proved (minimum- and maximum-degree versions) | [Lean](graffiti-179/Strong179.lean) · [Write-up](graffiti-179/README.md) |
| Graffiti.pc #180 | Open in general; bipartite, low-eccentricity and small-transversal cases proved | [Lean and replay](graffiti-180-partial/README.md) · [Exact triangle-chord certificate criteria](graffiti-180-chord-criteria/README.md) · [Full proof trail](PROOF-TRAILS.md#graffiti-pc-180) |
| Graffiti.pc #182 | Proved | [Lean](graffiti-182/Proof182.lean) · [Write-up](graffiti-182/README.md) |
| Graffiti.pc #183 | Proved | [Lean](graffiti-183/src/Proof183.lean) · [Written proof](graffiti-183/PROOF.md) |
| Graffiti.pc #184 | Disproved (22-vertex counterexample) | [Lean](graffiti-184/Counterexample184.lean) · [Write-up](graffiti-184/README.md) |
| Graffiti.pc #185 | Disproved (22-vertex counterexample) | [Lean](graffiti-185/Counterexample185.lean) · [Write-up](graffiti-185/README.md) |
| Graffiti.pc #186 | Literal statement disproved; external-neighborhood variant proved | [Lean counterexample](graffiti-186/Counterexample186.lean) · [Lean proof](graffiti-186/External186.lean) · [Write-up](graffiti-186/README.md) |
| Graffiti.pc #189 | Open in general; full degree-four case, connectivity ≥ d − 1 (d ≥ 3), and triangle-free 2-connected graphs proved in Lean | [Near-connectivity](graffiti-189-near/README.md) · [Triangle-free](graffiti-189-triangle-free/README.md) · [Full proof trail](PROOF-TRAILS.md#graffiti-pc-189) |
| Graffiti.pc #199 | Open in general; proved at vertex connectivity 1 and 2 | [Lean and replay](graffiti-199-low-connectivity/README.md) · [Small-cut Hamiltonian configurations](graffiti-199-small-cut-configurations/README.md) · [Full proof trail](PROOF-TRAILS.md#graffiti-pc-199) |
| Graffiti.pc #208 | Proved | [Lean](graffiti-208/Proof208.lean) |
| Graffiti.pc #232 | Proved | [Lean](graffiti-232/Formal232.lean) · [Write-up](graffiti-232/README.md) |
| Graffiti.pc #235 | Proved | [Lean](graffiti-235/Exact235.lean) · [Write-up](graffiti-235/README.md) |
| Graffiti.pc #241 | Proved | [Lean](graffiti-241/Proof241.lean) · [Prior stronger bound: Gebendorfer](https://www.researchgate.net/publication/410896645_Closed-Neighborhood_Components_Open_Packings_and_Total_Domination_in_Trees) |
| Graffiti.pc #242 | Proved | [Lean](graffiti-242/Proof242.lean) |
| Graffiti.pc #247 | Disproved | [Lean](graffiti-247/Proof247.lean) |
| Graffiti.pc #252 | Disproved | [Lean](graffiti-252/Counterexample252.lean) · [Prior: Jonas Gebendorfer](https://www.researchgate.net/publication/414086193_A_30-vertex_C_4_-free_counterexample_to_WOWII_Conjecture_252) |
| Graffiti.pc #253 | Disproved | [Lean](graffiti-253/Counterexample253.lean) · [Prior: Jonas Gebendorfer](https://www.researchgate.net/publication/415561278_A_girth-five_counterexample_to_Written_on_the_Wall_II_Conjecture_253) |
| Graffiti.pc #255 | Disproved | [Lean](graffiti-255/Counterexample255.lean) · [Write-up](graffiti-255/README.md) · [Parallel: Derek Blair](https://github.com/derekblair/math-proofs/blob/98bc251740a3194ff742206feadc1e90fe4d1c6c/research/lean-verified-2026-11-25/README.md) |
| Graffiti.pc #258 | Proved | [Lean](graffiti-258-259/Formal258.lean) · [Write-up](graffiti-258-259/README.md) |
| Graffiti.pc #259 | Proved | [Lean](graffiti-258-259/Formal259.lean) · [Write-up](graffiti-258-259/README.md) |
| Graffiti.pc #260 | Proved | [Lean](graffiti-260/Formal260.lean) · [Write-up](graffiti-260/README.md) |
| Graffiti.pc #261 | Proved | [Lean](graffiti-261/Formal261.lean) · [Write-up](graffiti-261/README.md) |
| Graffiti.pc #267 | Disproved | [Lean](graffiti-267/Counterexample267.lean) · [Prior disproof: Claude Opus 5 / AI Village](https://grok-ai-village-news-496089.gitlab.io/articles/opus5-wow2-conj267-false-one-hundred-sixty-seven) |
| Graffiti.pc #268 | Proved | [Lean](graffiti-268/Proof268.lean) · [Parallel: Derek Blair](https://github.com/derekblair/math-proofs/blob/98bc251740a3194ff742206feadc1e90fe4d1c6c/research/lean-verified-2026-11-25/README.md) |
| Graffiti.pc #271 | Proved | [Lean](graffiti-271/Proof271.lean) · [Write-up](graffiti-271/README.md) · [Parallel: Derek Blair](https://github.com/derekblair/math-proofs/blob/98bc251740a3194ff742206feadc1e90fe4d1c6c/research/lean-verified-2026-11-25/README.md) |
| Graffiti.pc #281 | Disproved | [Lean](graffiti-281/Counterexample281.lean) · [Prior disproof: Claude Opus 5 / AI Village](https://grok-ai-village-news-496089.gitlab.io/articles/opus5-graffiti-conj281-total-domination-2corona-bridge.html) |
| Graffiti.pc #287 | Disproved | [Lean](graffiti-287/Counterexample287.lean) · [Prior disproof: Claude Opus 5 / AI Village](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/raw/main/verify/verify_conj287.py) |
| Graffiti.pc #290 | Proved | [Lean](graffiti-290/Proof290.lean) |
| Graffiti.pc #299 | Proved | [Lean](graffiti-299/Proof299.lean) · [Transversal bound](https://doi.org/10.1007/BF01191201) |
| Graffiti.pc #302 | Disproved | [Lean](graffiti-302/Counterexample302.lean) |
| Graffiti.pc #304 | Proved (nonempty complement); disproved (empty maximum = 0) | [Lean](graffiti-304/Proof304.lean) · [Earlier corona case](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/raw/main/notes/2026-08-24_wow2_mar2007_gammat_block.md) |
| Graffiti.pc #305 | Proved (nonempty complement); disproved (empty maximum = 0) | [Lean](graffiti-305/Proof305.lean) |
| Graffiti.pc #308 | Disproved | [Lean](graffiti-308/Counterexample308.lean) · [Earlier AI Village counterexample](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/raw/main/verify/verify_wow2_308.py) |
| Graffiti.pc #310 | Proved | [Lean](graffiti-310/Formal310.lean) · [Write-up](graffiti-310/README.md) |
| Graffiti.pc #314 | Proved | [Lean 4.19](graffiti-314/Proof314.lean) · [Earlier Lean proof by Chitty and Landers](https://github.com/glyaea/wow-ii-314/blob/7b35f1252e4aaae3c787faf8091f9c7cd4edc41f/solution.lean) |
| Graffiti.pc #315 | Proved | [Lean](graffiti-315/Proof315.lean) |
| Graffiti.pc #317 | Proved | [Lean](graffiti-317/Proof317.lean) |
| Graffiti.pc #318 | Proved | [Lean](graffiti-318/Proof318.lean) |
| Graffiti.pc #320 | Proved | [Lean](graffiti-320/Proof320.lean) · [Earlier AI Village status report](https://grok-ai-village-news-496089.gitlab.io/articles/opus5-wow2-conj309-false-one-hundred-fifty-nine) |
| Graffiti.pc #321 | Proved | [Lean](graffiti-321/Proof321.lean) · [Earlier AI Village proof](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/blob/main/README.md#7fl2-conjecture-321-is-vacuously-true-above-order-six) |
| Graffiti.pc #323 | Proved | [Lean](graffiti-323/Proof323.lean) · [Earlier AI Village proof, §7fj](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/blob/main/README.md#7fj5-the-theorem) |
| Graffiti.pc #324 | Proved | [Lean](graffiti-324/Proof324.lean) · [Earlier partial results, §7fn](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/blob/main/README.md#7fn-written-on-the-wall-ii-conjecture-324-a-complete-reduction-to-cores-and-a-residue-ceiling-that-blocks-every-counterexample-i-can-construct) |
| Graffiti.pc #325 | Proved | [Lean](graffiti-325/Proof325.lean) · [Earlier AI Village proof, §7fk](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/blob/main/README.md#7fk4-the-structure-theorem-and-the-proof) |
| Graffiti.pc #326 | Proved | [Lean](graffiti-326/Proof326.lean) · [Earlier AI Village status report](https://grok-ai-village-news-496089.gitlab.io/articles/opus5-wow2-conj309-false-one-hundred-fifty-nine) |
| Graffiti.pc #342 | Proved | [Lean](graffiti-342/Proof342.lean) · [From published #332](https://math1um.github.io/Research/r08.pdf) |
| Graffiti.pc #344 | Proved | [Lean](graffiti-344/Proof344.lean) · [From published #332](https://math1um.github.io/Research/r08.pdf) |
| Graffiti.pc #348 | Proved | [Lean](graffiti-348/Proof348.lean) |
| Graffiti.pc #351 | Disproved | [Lean](graffiti-351/Counterexample351.lean) |
| Graffiti.pc #354 | Disproved | [Lean](graffiti-354/Counterexample354.lean) · [Earlier coefficient-1 variant](https://www.researchgate.net/publication/410896645_Closed-Neighborhood_Components_Open_Packings_and_Total_Domination_in_Trees) |
| Graffiti.pc #356 | Proved | [Lean](graffiti-356/Proof356.lean) |
| Graffiti.pc #361 | Proved | [Lean](graffiti-361/Verify361.lean) · [Write-up](graffiti-361/README.md) |
| Graffiti.pc #362 | Proved | [Lean](graffiti-362/Formal362.lean) · [Write-up](graffiti-362/README.md) |
| Graffiti.pc #363 | Disproved | [Lean](graffiti-363/Counterexample363.lean) · [Gebendorfer’s earlier Lean counterexample](https://github.com/google-deepmind/formal-conjectures/issues/7360) · [Counterexample even at coefficient 1/3](graffiti-363/CounterexampleOneThird.lean) |
| Graffiti.pc #365 | Proved | [Lean](graffiti-365/Proof365.lean) |
| Graffiti.pc #367 | Proved (unique mode); disproved (ties allowed) | [Lean](graffiti-367/Proof367.lean) |
| Graffiti.pc #369 | Disproved | [Lean](graffiti-369/Counterexample369.lean) |
| Graffiti.pc #372 | Proved | [Lean](graffiti-372/Proof372.lean) (defined domain: path cover ≥ 2) · [Gebendorfer’s earlier proof](https://www.researchgate.net/publication/417064608_Total_domination_and_vertex_covers_of_trees_covered_by_two_paths_A_resolution_of_Written_on_the_Wall_II_Conjecture_372_on_its_defined_domain) |
| Graffiti.pc #376 | Proved | [Lean](graffiti-376/Proof376.lean) |
| Graffiti.pc #377 | Proved | [Lean](graffiti-377/Proof377.lean) |
| Graffiti.pc #379 | Proved | [Lean](graffiti-379/Exact379.lean) |
| Graffiti.pc #380 | Proved where defined; undefined on some trees | [Lean](graffiti-380/Proof380.lean) |
| Graffiti.pc #381 | Proved | [Lean](graffiti-381/Formal381.lean) · [Write-up](graffiti-381/README.md) |
| Graffiti.pc #384b | Open in general; at most one above bound; exact with up to four triangle counts | [Lean and replay](graffiti-384b-partial/README.md) · [Order-34 reduction](graffiti-384b-order34/README.md) · [Full proof trail](PROOF-TRAILS.md#graffiti-pc-384b) |
| Graffiti.pc #394 | Disproved | [Lean](graffiti-394/Counterexample394.lean) |
| Graffiti.pc #397c | Proved | [Lean](graffiti-397c/Proof397c.lean) · [Gebendorfer’s earlier proof](https://doi.org/10.13140/RG.2.2.34978.18880) |
| Graffiti.pc #398 | Disproved | [Lean](graffiti-398/Counterexample398.lean) · [Dubey’s earlier counterexample](https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa#wowii-398) |
| Graffiti.pc #402 | Disproved | [Lean](graffiti-402/Counterexample402.lean) · [Earlier AI Village counterexample](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/blob/main/README.md#7ba-conjecture-402-of-written-on-the-wall-ii-is-false) |
| Graffiti.pc #412d | Proved | [Lean](graffiti-412d/Proof412d.lean) |
| Graffiti.pc #416 | Proved | [Lean](graffiti-416/Formal416.lean) · [Write-up](graffiti-416/README.md) |
| Graffiti.pc #422a | Disproved | [Lean](graffiti-422a/Proof422a.lean) · [AI Village’s earlier counterexample](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/blob/main/verify/verify_conj422a.py) |
| Graffiti.pc #426 | Proved | [Lean](graffiti-426/Formal426.lean) · [Write-up](graffiti-426/README.md) · [Prior: Siddhant Dubey](https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa) |
| Graffiti.pc #427 | Disproved | [Lean](graffiti-427/Counterexample427.lean) (corrected cut-vertex statement) · [Prior disproofs of other readings](https://hexagonmath.org/pdf/2610.00500v1#page=6) |
| Graffiti.pc #432b | Proved | [Lean](graffiti-432b/Proof432b.lean) |
| Graffiti.pc #433 | Disproved | [Lean](graffiti-433/Proof433.lean) |
| Graffiti.pc #438a | Proved | [Lean](graffiti-438a/Proof438a.lean) |
| Graffiti.pc #438b | Proved | [Lean](graffiti-438b/Proof438b.lean) |
| Graffiti.pc #439 | Disproved | [Lean](graffiti-439/Counterexample439.lean) · [AI Village witness](https://gitlab.com/ai-village-agents/village/graffiti-verification/-/raw/a600543/verify/verify_wow2_439.py) · [Dubey’s earlier witness](https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa#wowii-439) |
| Graffiti.pc #442 | Disproved | [Lean](graffiti-442/Counterexample442.lean) · [AI Village witness](https://grok-ai-village-news-496089.gitlab.io/articles/opus5-wow2-conj442-false-one-hundred-sixty-two) · [Dubey’s earlier witness](https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa#wowii-442) |
| Graffiti.pc #444 | Disproved | [Lean](graffiti-444/Exact444.lean) · [Write-up](graffiti-444/README.md) · [Prior: Siddhant Dubey](https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa) |
| Graffiti.pc #446 | Proved | [Lean](graffiti-446/Verify446.lean) · [Write-up](graffiti-446/README.md) · [Prior: Siddhant Dubey](https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa) |
| Graffiti.pc #448a | Proved | [Lean](graffiti-448a/Formal448a.lean) · [Write-up](graffiti-448a/README.md) · [Prior: Siddhant Dubey](https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa) |
| Graffiti.pc #449 | Proved | [Lean](graffiti-449/Formal449.lean) · [Write-up](graffiti-449/README.md) · [Prior: Siddhant Dubey](https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa) |
| Graffiti.pc #450 | Proved | [Lean](graffiti-450/Formal450.lean) · [Write-up](graffiti-450/README.md) · [Prior: Siddhant Dubey](https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa) |

<a id="graffiti-3-index"></a>

## Graffiti³

| Problem | Resolution status | References |
|---|---|---|
| Graffiti³ #14 | Proved | [Lean](graffiti3-14/Totient14.lean) · [Write-up](graffiti3-14/README.md) |
| Graffiti³ #15(a) | Disproved | [Lean](graffiti3-15a/Proof15a.lean) |
| Graffiti³ #21 | Disproved | [Lean](graffiti3-21/Proof21.lean) |
| Graffiti³ #22 | Disproved | [Lean](graffiti3-22/Proof22.lean) |
| Graffiti³ #25 | Proved | [Lean](graffiti3-25/Proof25.lean) |
| Graffiti³ #27 | Disproved | [Lean](graffiti3-27/Dihedral27.lean) · [Write-up](graffiti3-27/README.md) |

## AutoGraphForge

| Problem | Resolution status | References |
|---|---|---|
| AutoGraphForge line 33 | Disproved; gap unbounded | [Lean and replay](autographforge-33/README.md) |
| AutoGraphForge line 66 | Disproved | [Lean](autographforge-66/PowerBurning.lean) |
| AutoGraphForge line 105 | Proved in Lean | [Component equality and four-vertex hereditary test](autographforge-105/README.md) |
| AutoGraphForge line 143 | Proved (consequence of cograph decomposition) | [Lean](autographforge-cograph/CographRadius.lean) · [Conventions and replay](autographforge-cograph/README.md) |
| AutoGraphForge line 187 | Disproved | [Lean](autographforge-book-tail/BookTail.lean) · [Replay](autographforge-book-tail/README.md) |
| AutoGraphForge line 188 | Proved in Lean | [Power domination versus two-forcing on cographs](autographforge-188/README.md) |
| AutoGraphForge line 221 | Disproved | [Lean](autographforge-book-tail/BookTail.lean) · [Replay](autographforge-book-tail/README.md) |
| AutoGraphForge line 242 | Proved in Lean; three-rainbow number equals order | [Proof](autographforge-242/) |
| AutoGraphForge line 303 | Disproved | [Lean](autographforge-303/AutoGraphForgePlanar.lean) |
| AutoGraphForge line 304 | Disproved | [Lean](autographforge-304/AutoGraphForge304.lean) |
| AutoGraphForge line 353 | Disproved | [Lean](autographforge-353/AutoGraphForge353.lean) |
| AutoGraphForge line 354 | Disproved | [Lean](autographforge-354/AutoGraphForge354.lean) |
| AutoGraphForge line 355 | Proved | [Lean](autographforge-355/AutoGraphForge355.lean) |
| AutoGraphForge line 357 | Disproved (singleton rainbow convention) | [Lean](autographforge-357/AutoGraphForge357.lean) |
| AutoGraphForge line 359 | Proved | [Lean](autographforge-359/AutoGraphForge359.lean) |
| AutoGraphForge line 362 | Disproved in Lean by a 17-vertex bipartite graph | [Counterexample](autographforge-362/README.md) |
| AutoGraphForge line 365 | Disproved | [Lean](autographforge-365/AutoGraphForgeDiamonds.lean) |
| AutoGraphForge line 370 | Proved where outer-connected domination is defined | [Lean](autographforge-370/OuterForest.lean) · [Replay](autographforge-370/README.md) |
| AutoGraphForge line 371 | Proved (where total forcing is defined) | [Lean](autographforge-371/AutoGraphForge371.lean) |
| AutoGraphForge line 372 | Proved (singleton rainbow convention) | [Lean](autographforge-372/AutoGraphForge372.lean) |
| AutoGraphForge line 373 | Proved (formalization of a known consequence) | [Lean](autographforge-373/AutoGraphForge373.lean) · [Prior formulas](https://doi.org/10.1090/surv/270) |
| AutoGraphForge line 376 | Disproved | [Lean](autographforge-365/AutoGraphForgeDiamonds.lean) |
| AutoGraphForge line 377 | Proved | [Lean](autographforge-377/AutoGraphForge377.lean) |
| AutoGraphForge line 378 | Proved | [Lean](autographforge-378/AutoGraphForge378.lean) |
| AutoGraphForge line 379 | Proved | [Lean](autographforge-379/AutoGraphForge379.lean) |
| AutoGraphForge line 383 | Disproved upstream; unbounded gap proved in Lean | [Planar chordal family](autographforge-book-forts/README.md) |
| AutoGraphForge line 464 | Disproved in Lean; unbounded gap even for bipartite planar graphs | [Proof](autographforge-464/) |
| AutoGraphForge line 500 | Proved in Lean by cograph join decomposition | [Lean](autographforge-500/JoinOuter.lean) |
| AutoGraphForge line 501 | Disproved | [Lean](autographforge-eulerian-chain/Chain.lean) · [Replay](autographforge-eulerian-chain/README.md) |
| AutoGraphForge line 534 | Proved in Lean; exact inequality and equality conditions for joins | [autographforge-534/](autographforge-534/) |
| AutoGraphForge line 567 | Disproved upstream; unbounded gap proved in Lean | [Planar chordal family](autographforge-book-forts/README.md) |
| AutoGraphForge line 574 | Disproved in Lean; sharp replacement and unbounded Eulerian gap | [Proof](autographforge-574/) |
| AutoGraphForge line 579 | Proved in Lean without the bipartite restriction | [Proof](autographforge-579/) |
| AutoGraphForge line 583 | Proved in Lean; sharp Slater bound for edge domination | [Proof](autographforge-583/) |
| AutoGraphForge line 595 | Disproved in Lean (22 vertices; known matching construction) | [Proof](autographforge-595/README.md) |
| AutoGraphForge line 621 | Proved in Lean; extends to quasi-line graphs | [Proof](autographforge-621/README.md) |
| AutoGraphForge line 645 | Proved in Lean; the same bound holds for all subcubic graphs | [Lean](autographforge-rainbow-vertex-cover/RainbowVertexCover.lean) · [Replay](autographforge-rainbow-vertex-cover/README.md) |
| AutoGraphForge line 659 | Disproved in Lean; unbounded gap on bipartite planar graphs | [Proof](autographforge-659/) |
| AutoGraphForge line 671 | Proved in Lean; the same bound holds for all subcubic graphs | [Lean](autographforge-rainbow-vertex-cover/RainbowVertexCover.lean) · [Replay](autographforge-rainbow-vertex-cover/README.md) |
| AutoGraphForge line 676 | Disproved in Lean by a connected 21-vertex chordal K₄-free graph | [Lean](autographforge-676/Chordal676.lean) · [Replay](autographforge-676/README.md) |
| AutoGraphForge line 711 | Proved in Lean; sharp on the triangle; literal line 6318 has a singleton counterexample | [autographforge-711/](autographforge-711/) |
| AutoGraphForge line 720 | Proved in Lean; sharp on K₂ | [Proof](autographforge-720/README.md) |
| AutoGraphForge line 747 | Disproved | [Lean](autographforge-shared-hub/SharedHub.lean) · [Replay](autographforge-shared-hub/README.md) |
| AutoGraphForge line 764 | Disproved | [Lean](autographforge-eulerian-chain/Chain.lean) · [Replay](autographforge-eulerian-chain/README.md) |
| AutoGraphForge line 791 | Disproved in Lean; witness also applies to lines 2732, 3754 and 5177 | [autographforge-791/](autographforge-791/) |
| AutoGraphForge line 808 | Proved (where total forcing is defined) | [Lean](autographforge-371/AutoGraphForge371.lean) |
| AutoGraphForge line 818 | Proved on GraphCalc's connected domain; false with +∞ disconnected diameter | [Lean](autographforge-cograph/CographRadius.lean) · [Conventions and replay](autographforge-cograph/README.md) |
| AutoGraphForge line 821 | Proved on GraphCalc's connected domain (known corollary); false if disconnected diameter is +∞ | [Lean](autographforge-821/ForestSlater.lean) · [Conventions and replay](autographforge-821/README.md) |
| AutoGraphForge line 832 | Disproved in Lean by the 22-vertex cubic witness | [Lean](autographforge-cubic-odd-blocks/Transfer.lean) |
| AutoGraphForge line 837 | Disproved in Lean by the 22-vertex cubic witness | [Lean](autographforge-cubic-odd-blocks/Transfer.lean) |
| AutoGraphForge line 838 | Disproved in Lean by the 22-vertex cubic witness | [Lean](autographforge-cubic-odd-blocks/Transfer.lean) |
| AutoGraphForge line 839 | Disproved in Lean by the 22-vertex cubic witness; equivalent to line 840 in this class | [Lean](autographforge-cubic-odd-blocks/Transfer.lean) |
| AutoGraphForge line 840 | Disproved in Lean by the 22-vertex cubic witness | [Lean](autographforge-cubic-odd-blocks/Transfer.lean) |
| AutoGraphForge line 841 | Disproved in Lean by the 22-vertex cubic witness; equivalent to line 837 in this class | [Lean](autographforge-cubic-odd-blocks/Transfer.lean) |
| AutoGraphForge line 842 | Disproved in Lean by a connected 14-vertex planar graph | [Lean](autographforge-842/Plane842.lean) · [Replay](autographforge-842/README.md) |
| AutoGraphForge line 843 | Disproved in Lean by the 22-vertex cubic witness | [Lean](autographforge-cubic-odd-blocks/Transfer.lean) |
| AutoGraphForge line 844 | Disproved in Lean by the 22-vertex cubic witness; equivalent to line 837 | [Lean](autographforge-cubic-odd-blocks/Transfer.lean) |
| AutoGraphForge line 845 | Disproved in Lean by the 22-vertex cubic witness; equivalent to line 840 | [Lean](autographforge-cubic-odd-blocks/Transfer.lean) |
| AutoGraphForge line 846 | Disproved in Lean by the 22-vertex cubic witness; equivalent to line 840 | [Lean](autographforge-cubic-odd-blocks/Transfer.lean) |
| AutoGraphForge line 847 | Disproved in Lean by the 22-vertex cubic witness; equivalent to line 837 | [Lean](autographforge-cubic-odd-blocks/Transfer.lean) |
| AutoGraphForge line 848 | Disproved in Lean by the 22-vertex cubic witness; equivalent to line 837 | [Lean](autographforge-cubic-odd-blocks/Transfer.lean) |
| AutoGraphForge line 849 | Disproved in Lean by the 22-vertex cubic witness; equivalent to line 840 | [Lean](autographforge-cubic-odd-blocks/Transfer.lean) |
| AutoGraphForge line 850 | Disproved in Lean by the 22-vertex cubic witness; equivalent to line 840 | [Lean](autographforge-cubic-odd-blocks/Transfer.lean) |
| AutoGraphForge line 851 | Disproved in Lean by the 22-vertex cubic witness; equivalent to line 837 | [Lean](autographforge-cubic-odd-blocks/Transfer.lean) |
| AutoGraphForge line 877 | Disproved | [Lean](autographforge-book-tail/BookTail.lean) · [Replay](autographforge-book-tail/README.md) |
| AutoGraphForge line 895 | Disproved | [Lean](autographforge-895/LineBouquet.lean) · [Replay](autographforge-895/README.md) |
| AutoGraphForge line 942 | Disproved | [Lean](autographforge-balanced-forcing/BalancedForcing.lean) |
| AutoGraphForge line 1078 | Proved in Lean; sharp at every positive regular degree | [Proof](autographforge-1078/) |
| AutoGraphForge line 1080 | Disproved (singleton rainbow convention) | [Lean](autographforge-1080/AutoGraphForge1080.lean) |
| AutoGraphForge line 1121 | Proved in Lean by a sharp Hall matching bound | [Proof](autographforge-1121/) |
| AutoGraphForge line 1125 | Proved in Lean (hereditary claw/bull characterization) | [Proof](autographforge-1125/README.md) |
| AutoGraphForge line 1128 | Proved on GraphCalc's numerical triameter domain | [Lean](autographforge-cograph/CographRadius.lean) · [Conventions and replay](autographforge-cograph/README.md) |
| AutoGraphForge line 1130 | Disproved in Lean by C160; upstream implicit witness also exists | [Proof](autographforge-1130/) |
| AutoGraphForge line 1132 | Proved in Lean; all nontrivial trees and sharp cycle-rank extension | [autographforge-1132/](autographforge-1132/) |
| AutoGraphForge line 1160 | Disproved in Lean by a 22-vertex cubic graph; exact perfect-matching criterion | [Proof](autographforge-1160/) |
| AutoGraphForge line 1161 | Disproved in Lean by the 22-vertex cubic witness; equivalent to line 1160 | [Lean](autographforge-cubic-odd-blocks/Transfer.lean) |
| AutoGraphForge line 1162 | Disproved in Lean by the 22-vertex cubic witness; equivalent to line 1160 | [Lean](autographforge-cubic-odd-blocks/Transfer.lean) |
| AutoGraphForge line 1173 | Proved in Lean by the cograph-tree star profile | [Lean](autographforge-cograph-trees/Rows.lean) · [Replay](autographforge-cograph-trees/README.md) |
| AutoGraphForge line 1178 | Proved in Lean by the cograph-tree star profile | [Lean](autographforge-cograph-trees/Rows.lean) · [Replay](autographforge-cograph-trees/README.md) |
| AutoGraphForge line 1181 | Proved in Lean by the cograph-tree star profile | [Lean](autographforge-cograph-trees/Rows.lean) · [Replay](autographforge-cograph-trees/README.md) |
| AutoGraphForge line 1212 | Proved in Lean by the cograph-tree star profile | [Lean](autographforge-cograph-trees/Rows.lean) · [Replay](autographforge-cograph-trees/README.md) |
| AutoGraphForge line 1215 | Proved in Lean by the cograph-tree star profile | [Lean](autographforge-cograph-trees/Rows.lean) · [Replay](autographforge-cograph-trees/README.md) |
| AutoGraphForge line 1221 | Proved (formalization of a known consequence) | [Lean](autographforge-373/AutoGraphForge373.lean) · [Prior formulas](https://doi.org/10.1090/surv/270) |
| AutoGraphForge line 1227 | Proved in Lean by the cograph-tree star profile | [Lean](autographforge-cograph-trees/Rows.lean) · [Replay](autographforge-cograph-trees/README.md) |
| AutoGraphForge line 1229 | Proved in Lean by the cograph-tree star profile | [Lean](autographforge-cograph-trees/Rows.lean) · [Replay](autographforge-cograph-trees/README.md) |
| AutoGraphForge line 1257 | Proved in Lean by the cograph-tree star profile | [Lean](autographforge-cograph-trees/Rows.lean) · [Replay](autographforge-cograph-trees/README.md) |
| AutoGraphForge line 1272 | Proved in Lean by the cograph-tree star profile | [Lean](autographforge-cograph-trees/Rows.lean) · [Replay](autographforge-cograph-trees/README.md) |
| AutoGraphForge line 1314 | Proved in Lean by the cograph-tree star profile | [Lean](autographforge-cograph-trees/Rows.lean) · [Replay](autographforge-cograph-trees/README.md) |
| AutoGraphForge line 1316 | Proved in Lean by the cograph-tree star profile | [Lean](autographforge-cograph-trees/Rows.lean) · [Replay](autographforge-cograph-trees/README.md) |
| AutoGraphForge line 1415 | Proved in Lean by the cograph-tree star profile | [Lean](autographforge-cograph-trees/Rows.lean) · [Replay](autographforge-cograph-trees/README.md) |
| AutoGraphForge line 1416 | Proved in Lean by the cograph-tree star profile | [Lean](autographforge-cograph-trees/Rows.lean) · [Replay](autographforge-cograph-trees/README.md) |
| AutoGraphForge line 1531 | Proved in Lean (connected equality exactly three paths) | [Proof](autographforge-1531/README.md) |
| AutoGraphForge line 1539 | Disproved | [Lean](autographforge-balanced-forcing/BalancedForcing.lean) |
| AutoGraphForge line 1553 | Proved in Lean (sharp general degree-excess bound) | [Proof](autographforge-1553/README.md) |
| AutoGraphForge line 1606 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-1606/) |
| AutoGraphForge line 1638 | Proved in Lean by the cograph-tree star profile | [Lean](autographforge-cograph-trees/Rows.lean) · [Replay](autographforge-cograph-trees/README.md) |
| AutoGraphForge line 1640 | Proved in Lean by the cograph-tree star profile | [Lean](autographforge-cograph-trees/Rows.lean) · [Replay](autographforge-cograph-trees/README.md) |
| AutoGraphForge line 1643 | Proved in Lean by the cograph-tree star profile | [Lean](autographforge-cograph-trees/Rows.lean) · [Replay](autographforge-cograph-trees/README.md) |
| AutoGraphForge line 1644 | Proved in Lean by the cograph-tree star profile | [Lean](autographforge-cograph-trees/Rows.lean) · [Replay](autographforge-cograph-trees/README.md) |
| AutoGraphForge line 1656 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-1656/) |
| AutoGraphForge line 1707 | Disproved in Lean; unbounded gap on connected claw-free graphs | [Proof](autographforge-1707/) |
| AutoGraphForge line 1813 | Disproved in Lean by all cliques of order at least 37 | [Lean](autographforge-1813/CliqueHarmonic.lean) |
| AutoGraphForge line 1839 | Disproved | [Lean](autographforge-365/AutoGraphForgeDiamonds.lean) |
| AutoGraphForge line 1883 | Disproved (singleton rainbow convention) | [Lean](autographforge-1883/AutoGraphForge1883.lean) |
| AutoGraphForge line 1889 | Disproved | [Lean](autographforge-shared-hub/SharedHub.lean) · [Replay](autographforge-shared-hub/README.md) |
| AutoGraphForge line 1891 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-1891/) |
| AutoGraphForge line 1900 | Proved in Lean; equality exactly for even cycles | [autographforge-1900/](autographforge-1900/) |
| AutoGraphForge line 1904 | Disproved | [Lean](autographforge-balanced-forcing/BalancedForcing.lean) |
| AutoGraphForge line 1908 | Disproved | [Lean](autographforge-303/AutoGraphForgePlanar.lean) |
| AutoGraphForge line 1915 | Disproved; unbounded gap on triangle chains | [Lean](autographforge-1915/TriangleChain.lean) · [Replay](autographforge-1915/README.md) |
| AutoGraphForge line 1956 | Disproved | [Lean](autographforge-balanced-forcing/BalancedForcing.lean) |
| AutoGraphForge line 1957 | Disproved in Lean (14 vertices; sharp degree-dependent bound) | [Proof](autographforge-1957/README.md) |
| AutoGraphForge line 1974 | Disproved | [Lean](autographforge-complete/CompleteRows.lean) |
| AutoGraphForge line 2039 | Disproved in Lean by a connected 10-vertex graph | [Counterexample](autographforge-2039/README.md) |
| AutoGraphForge line 2054 | Disproved | [Lean](autographforge-friendship/Friendship.lean) |
| AutoGraphForge line 2055 | Proved in Lean; sharp on the 10-vertex path (known burning bound corollary) | [Proof](autographforge-2055/README.md) |
| AutoGraphForge line 2088 | Disproved (singleton rainbow convention) | [Lean](autographforge-1883/AutoGraphForge1883.lean) |
| AutoGraphForge line 2175 | Disproved | [Lean](autographforge-star/StarCone.lean) |
| AutoGraphForge line 2194 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-2194/) |
| AutoGraphForge line 2206 | Disproved | [Lean](autographforge-star/StarCone.lean) |
| AutoGraphForge line 2222 | Disproved | [Lean](autographforge-balanced-forcing/BalancedForcing.lean) |
| AutoGraphForge line 2223 | Disproved in Lean by an 11-vertex bipartite graph | [Counterexample](autographforge-2223/README.md) |
| AutoGraphForge line 2240 | Disproved | [Lean](autographforge-balanced-forcing/BalancedForcing.lean) |
| AutoGraphForge line 2255 | Disproved | [Lean](autographforge-balanced-forcing/BalancedForcing.lean) |
| AutoGraphForge line 2276 | Proved in Lean; sharp on the 17-vertex cycle (known burning bound corollary) | [Proof](autographforge-2276/README.md) |
| AutoGraphForge line 2290 | Disproved | [Lean](autographforge-friendship/Friendship.lean) |
| AutoGraphForge line 2304 | Disproved | [Lean](autographforge-friendship/Friendship.lean) |
| AutoGraphForge line 2319 | Disproved | [Lean](autographforge-balanced-forcing/BalancedForcing.lean) |
| AutoGraphForge line 2320 | Disproved | [Lean](autographforge-balanced-forcing/BalancedForcing.lean) |
| AutoGraphForge line 2321 | Disproved | [Lean](autographforge-balanced-forcing/BalancedForcing.lean) |
| AutoGraphForge line 2334 | Disproved | [Lean](autographforge-2334/BranchedTree.lean) · [Replay](autographforge-2334/README.md) |
| AutoGraphForge line 2339 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-2339/) |
| AutoGraphForge line 2348 | Disproved | [Lean](autographforge-complete/CompleteRows.lean) |
| AutoGraphForge line 2354 | Disproved | [Lean](autographforge-balanced-forcing/BalancedForcing.lean) |
| AutoGraphForge line 2355 | Disproved | [Lean](autographforge-complete/CompleteRows.lean) |
| AutoGraphForge line 2376 | Disproved | [Lean](autographforge-balanced-forcing/BalancedForcing.lean) |
| AutoGraphForge line 2380 | Disproved | [Lean](autographforge-friendship/Friendship.lean) |
| AutoGraphForge line 2394 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-2394/) |
| AutoGraphForge line 2395 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-2395/) |
| AutoGraphForge line 2396 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-2396/) |
| AutoGraphForge line 2400 | Disproved | [Lean](autographforge-complete/CompleteRows.lean) |
| AutoGraphForge line 2405 | Disproved | [Lean](autographforge-friendship/Friendship.lean) |
| AutoGraphForge line 2406 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-2406/) |
| AutoGraphForge line 2409 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-2409/) |
| AutoGraphForge line 2411 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-2411/) |
| AutoGraphForge line 2417 | Disproved | [Lean](autographforge-star/StarCone.lean) |
| AutoGraphForge line 2425 | Disproved | [Lean](autographforge-complete/CompleteRows.lean) |
| AutoGraphForge line 2427 | Disproved (singleton rainbow convention) | [Lean](autographforge-1883/AutoGraphForge1883.lean) |
| AutoGraphForge line 2437 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-2437/) |
| AutoGraphForge line 2452 | Disproved | [Lean](autographforge-multipartite/Multipartite.lean) |
| AutoGraphForge line 2453 | Disproved | [Lean](autographforge-multipartite/Multipartite.lean) |
| AutoGraphForge line 2471 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-2471/) |
| AutoGraphForge line 2473 | Disproved in Lean by the same connected graph as line 2039 | [Counterexample](autographforge-2473/README.md) |
| AutoGraphForge line 2474 | Disproved | [Lean](autographforge-multipartite/Multipartite.lean) |
| AutoGraphForge line 2482 | Disproved | [Lean](autographforge-multipartite/Multipartite.lean) |
| AutoGraphForge line 2494 | Disproved | [Lean](autographforge-star/StarCone.lean) |
| AutoGraphForge line 2508 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-2508/) |
| AutoGraphForge line 2512 | Disproved | [Lean](autographforge-star/StarCone.lean) |
| AutoGraphForge line 2517 | Disproved; also follows from line 33 | [Lean](autographforge-shared-hub/SharedHub.lean) · [Replay](autographforge-shared-hub/README.md) |
| AutoGraphForge line 2526 | Disproved | [Lean](autographforge-complete/CompleteRows.lean) |
| AutoGraphForge line 2527 | Disproved in Lean (archived witnesses and unbounded planar family) | [Proof](autographforge-2527/README.md) |
| AutoGraphForge line 2535 | Disproved in Lean by a 24-vertex connected planar graph | [Lean](autographforge-2535/Plane2535.lean) · [Replay](autographforge-2535/README.md) |
| AutoGraphForge line 2537 | Disproved | [Lean](autographforge-friendship/Friendship.lean) |
| AutoGraphForge line 2553 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-2553/) |
| AutoGraphForge line 2560 | Proved in Lean (sharp factor three and induced-bull packing refinement) | [Proof](autographforge-2560/README.md) |
| AutoGraphForge line 2562 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-2562/) |
| AutoGraphForge line 2572 | Disproved | [Lean](autographforge-complete/CompleteRows.lean) |
| AutoGraphForge line 2577 | Disproved | [Lean](autographforge-star/StarCone.lean) |
| AutoGraphForge line 2578 | Disproved | [Lean](autographforge-complete/CompleteRows.lean) |
| AutoGraphForge line 2579 | Disproved | [Lean](autographforge-complete/CompleteRows.lean) |
| AutoGraphForge line 2581 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-2581/) |
| AutoGraphForge line 2583 | Disproved in Lean by C43; upstream implicit witness also exists | [Proof](autographforge-2583/) |
| AutoGraphForge line 2590 | Disproved | [Lean](autographforge-friendship/Friendship.lean) |
| AutoGraphForge line 2595 | Disproved (singleton rainbow convention) | [Lean](autographforge-friendship/Friendship.lean) |
| AutoGraphForge line 2596 | Disproved by Forsad; independent Lean certificate | [Original counterexample](https://github.com/JanPastorek/AutoGraphForge/issues/1) · [Lean](autographforge-complete/CompleteRows.lean) |
| AutoGraphForge line 2598 | Disproved in Lean by an 11-vertex subcubic tree | [Counterexample](autographforge-2598/README.md) |
| AutoGraphForge line 2600 | Disproved | [Lean](autographforge-friendship/Friendship.lean) |
| AutoGraphForge line 2602 | Disproved (singleton rainbow convention) | [Lean](autographforge-friendship/Friendship.lean) |
| AutoGraphForge line 2603 | Disproved | [Lean](autographforge-complete/CompleteRows.lean) |
| AutoGraphForge line 2900 | Disproved in Lean by the 17-vertex star | [Lean](autographforge-star-implications/StarImplications.lean) |
| AutoGraphForge line 2901 | Disproved in Lean; transfers line 2417 | [Lean](autographforge-star-implications/StarImplications.lean) |
| AutoGraphForge line 2918 | Disproved in Lean by the 17-vertex star | [Lean](autographforge-star-implications/StarImplications.lean) |
| AutoGraphForge line 3232 | Disproved in Lean by the 22-vertex cubic witness | [Lean](autographforge-cubic-odd-implications/OddImplications.lean) · [Replay](autographforge-cubic-odd-implications/README.md) |
| AutoGraphForge line 3378 | Disproved in Lean by C43 | [Lean](autographforge-cycle-implications/CycleImplications.lean) |
| AutoGraphForge line 4293 | Disproved in Lean by C43; equivalent to line 3378 | [Lean](autographforge-cycle-implications/CycleImplications.lean) |
| AutoGraphForge line 4298 | Disproved in Lean by C43 | [Lean](autographforge-cycle-implications/CycleImplications.lean) |
| AutoGraphForge line 4862 | Disproved in Lean by the 22-vertex cubic witness | [Lean](autographforge-cubic-odd-implications/OddImplications.lean) · [Replay](autographforge-cubic-odd-implications/README.md) |
| AutoGraphForge line 5169 | Disproved in Lean; smallest witnesses at order 10, or 13 connected; equivalent line 3060 | [autographforge-5169/](autographforge-5169/) |
| AutoGraphForge line 5170 | Disproved in Lean | [autographforge-5170/](autographforge-5170/) |
| AutoGraphForge line 5174 | Proved in Lean; prior regular bound, with a degree-excess refinement | [autographforge-5174/](autographforge-5174/) |
| AutoGraphForge line 6567 | Disproved in Lean by the 17-vertex star | [Lean](autographforge-star-implications/StarImplications.lean) |
| AutoGraphForge line 6613 | Disproved in Lean; equivalent to line 2918 | [Lean](autographforge-star-implications/StarImplications.lean) |

## Erdős Problems

| Problem | Resolution status | References |
|---|---|---|
| Erdős Problem #324 | Open in general | [Lean-checked even-quartic collision families](erdos-324-even-quartic-collisions/) · [extension to 256 base coefficients and square multiples](erdos-324-even-quartic-collisions-256/) |

## Steinerberger’s Some Open Problems

| Problem | Resolution status | References |
|---|---|---|
| Bad Science Matrices, dimension 6 | Exact optimum proved in Lean | [End-to-end Lean proof](steinerberger-bad-science-six-complete/) · [Written proof](steinerberger-bad-science-six/) |
| Bad Science Matrices, dimension 7 | Exact optimum proved in Lean | [End-to-end Lean proof](steinerberger-bad-science-seven-complete/) · [Written proof](steinerberger-bad-science-seven/) |
| Bad Science Matrices, dimension 8 | Computational upper bound; attaining construction checked in Lean | [Proof sketch and checks](steinerberger-bad-science-eight/) |
