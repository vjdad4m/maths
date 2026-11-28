# Graffiti.pc #384b for 29 triangle-count types and 30 nonleaves

**Every finite simple graph with 29 distinct vertex triangle counts and 30 vertices of degree at least two has a two-dominating set of size at most |V(G)| − 15.** A two-dominating set contains at least two neighbors of each vertex outside it. A vertex's triangle count is the number of unordered triangles containing that vertex. Zero contributes to the set of counts whenever it is realized. The theorem also applies to disconnected graphs. [Original-graph theorem](OriginalSix30.lean)

Combining this result with the frozen 28-nonleaf theorem and its quota reduction gives `Graffiti384b.EarMix.remaining_nonleaves`. A failure at diversity 29 must have exactly 29 nonleaves. The separate 29-nonleaf case and the general conjecture remain outside this package.

## Sampling the three ears

Assume the claimed bound fails. The shared-neighbor theorem gives 27 vertices of degree at least three and three vertices of degree two, called ears. Each ear has two high-degree neighbors. The three pairs are disjoint. Induce on the 30 nonleaves. This preserves the triangle count at each retained vertex and both neighbors of each ear. The 27 high vertices have distinct counts, all at least two. The proof below gives a two-dominating set of size at most 15 in the induced graph. Including the vertices outside the core gives the claimed bound in the original graph. [Core construction and transfer](OriginalSix30.lean) · [Published result index](https://github.com/vjdad4m/maths/blob/main/README.md)

Let W be the 21 high vertices outside the three ear neighborhoods. Choose one of the three ears, then apply each of the following trials to every subset of W of the prescribed size.

| Family | Retained outside W | Sample size from W | Weight |
|---|---|---:|---:|
| First | Both neighbors of the chosen ear and the other two ears | 9 | 2 |
| Second | The chosen ear and both neighbors of each other ear | 8 | 5 |

Each trial starts with 13 retained vertices. Remove every sampled vertex whose neighborhood is a clique and which already has at least two retained neighbors. These removals are compatible. Two adjacent vertices with clique neighborhoods would have the same closed neighborhood and the same triangle count, whereas the sampled vertices have distinct counts. Every omitted vertex that loses a neighbor through this removal still sees the removed vertex's two retained neighbors. Add the initially omitted vertices with fewer than two retained neighbors. If the two-domination number were at least 16, every trial would need at least three more additions than these removals. [Simultaneous removal and counting lemma](SimplicialCredit30.lean)

Summing over the three choices of ear gives a required weighted excess of 14,447,790. The proof separately charges the 21 vertices of W and the six ear neighbors. For a vertex of W, its contacts with each of the three anchor pairs determine its fixed support in all six trials. The rank of its triangle count bounds its degree. At equality with the binomial triangle bound the vertex has a clique neighborhood, so the proof can count removals as well as additions. Each of the six anchors has only one ear neighbor and that ear is in at most one triangle. Its repair charge lies at least 175,032 below the corresponding rank bound. The 27 rank bounds sum to 15,220,634, giving an upper bound of **14,170,442** and a strict margin of **277,348**. [Integer bounds](EarMixtureRows.lean) · [Neighborhood identities](EarLayout30.lean) · [Sample counts](EarFiber30.lean) · [Required total](EarTotal30.lean) · [Summed rank comparison](SixAnchorSaving30.lean)

## Verification and provenance

The seven linked Lean files are the complete extension. It reuses `Shared29.residual_distinct` for the disjoint ear neighborhoods, `Repair.maximal_diversity` for the 27 triangle ranks, `Prune.counts_preserved` for induction, and the capacity lemmas for lifting. `Thin28.hit` and `HighSquare28.bill_bound` count deficiencies in fixed-size samples. The compatible clique-neighborhood removals adapt the argument in `PendantRank.clean` to arbitrary retained pins and to both complementary trials. `TwentyEight.remaining_counts` supplies the earlier reduction to 29 or 30 nonleaves.

Linear optimization suggested the two sample sizes and integer weights. Lean proves coverage for every graph in the theorem and checks the complete finite rank table using kernel reduction. The table is indexed by a rank, a degree within W, and the numbers of neighbors in each of the three pairs. The runner checks each of the 27 ranks separately to limit peak memory. The proof has no graph-enumeration assumption.

Two checked-mode replays respectively used the working source and an unpacked source bundle. Each authenticated the two frozen predecessor archives, 350 source hashes, and 350 predecessor objects. Each compiled the seven new modules with warnings as errors, matched all seven fresh object hashes, and verified 16 reports using only propext, Classical.choice, and Quot.sound. The runner scans all 357 selected project sources for proof placeholders, custom axiom declarations and native_decide. The archives contain two historical names with different file contents. For ThirdEar and AnchorScores, the replay uses the exact source hashes listed by the shared-anchor predecessor. The earlier 28-nonleaf build imports neither conflicting name. [Runner](replay.py) · [Predecessor sources](PRIOR-SOURCES.sha256) · [Predecessor objects](CHECKED-OBJECTS.tsv) · [New sources](NEW-SOURCES.sha256) · [New objects](NEW-OBJECTS.sha256)

Use Lean 4.19.0 at 6caaee842e94 and Mathlib v4.19.0 at c44e0c8ee63ca166450922a373c7409c5d26b00b. Set CROSSFOUR_LEAN_BIN and CROSSFOUR_MATHLIB to the local binary directory and Mathlib checkout as needed. Both verification modes use one Lean thread and synchronous elaboration. The first command uses the recorded predecessor objects in the shared workspace. The second command rebuilds all predecessors from the bundled source archives.

~~~sh
python3 -B replay.py --checked /absolute/path/to/shared/workspace
python3 -B replay.py --cold
~~~
