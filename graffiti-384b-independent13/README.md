# Graffiti.pc #384b — independent degree-two vertices with at least thirteen contacts

Let T be the set of distinct numbers of triangles incident with a vertex, including zero whenever realized. A set 2-dominates a graph when every vertex outside the set has at least two neighbors in it. The catalogue conjecture for a connected finite simple graph of order n > 2 asks whether its minimum 2-dominating set has size at most n − ⌈|T|/2⌉.

## Theorem

Let G be a finite simple graph on 33 vertices with 31 distinct triangle counts and 32 vertices of degree at least two. Suppose the degree-two vertices are pairwise nonadjacent. Fix a vertex e with N(e) = {a,b}, a ≠ b, and N(a) ∩ N(b) = {e}. Write h for the number of vertices outside {e,a,b} adjacent to a or b.

**If h ≥ 13, then γ₂(G) ≤ 17.** No hypothesis about connectedness, the degrees of a and b, their adjacency, or the location of the leaf is needed for this implication. In any counterexample in this independent branch, every ear satisfying the displayed intersection condition must therefore have h ≤ 12. The previous joint-ear theorem handled h ≥ 17. This result also covers h = 16, 15, 14 and 13. [Lean theorem exact_of_thirteen](IndependentThirteen.lean)

## Proof

Take a pool X of 27 vertices of degree at least three outside the two fixed anchors. Start with the complement of X plus a fixed-size sample from X. Complete the set by promoting omitted vertices that see fewer than two retained vertices. The existing joint-ear sampler allows removing every degree-two vertex all of whose pool neighbors were sampled. The new saving removes sampled vertices whose neighborhoods are cliques whenever two of their neighbors are retained.

Two adjacent vertices with clique neighborhoods have equal closed neighborhoods and hence equal degrees and triangle counts. The triangle counts in X are distinct in any putative counterexample. Thus all qualifying sampled vertices are pairwise nonadjacent, and their two witnesses survive simultaneous removal. Any newly affected omitted neighbor also sees these same two retained witnesses because it lies in the clique neighborhood. A vertex of degree at least three with a clique neighborhood cannot be adjacent to a degree-two vertex. The ear savings and the clique savings can therefore be counted together. An insertion into a smaller sample gives a lower bound on the number of times a given vertex qualifies. [Pointwise construction](SimplicialTrial.lean) · [Averaging](SimplicialRanks.lean)

For a sample of nine, let c be the number of incidences from the two other degree-two vertices to vertices outside X, counted with multiplicity. Let z indicate whether the unique remaining exterior vertex outside X and these two ears sees an anchor. A failure would require

```
453492 h + 581894 c + 453492 (1 − z) ≤ 6312902.
```

At h = 12 the inequality already forces c ≤ 1, and c = 1 requires z = 1. At h = 14 even the first term exceeds the allowance by 35,986. At h = 13 the remaining allowance is 417,506, which forces c = 0 and z = 1 for every admissible pool. Varying the pool then forces both anchors to have degree at least three. For X equal to the high vertices other than the anchors, all four other-ear incidences land in X. Exactly twelve anchor contacts land there. [Pool inequality and structural consequences](IndependentFrontier.lean)

Let x,y be the numbers of neighbors of the two anchors in this last pool, so x+y=12. The only possible triangle at an anchor involving a neighbor outside the pool is the distinguished ear triangle. Consequently the two anchor scores are bounded by 1+binom(x,2) and 1+binom(y,2). Either one score is at most 11 or both are at most 16. Both scores are distinct and excluded from the 27 exterior scores. The resulting lower bounds for the ordered exterior scores sharpen the ten-vertex sampling estimate. The table gives an upper bound of 34,302,106 after accounting for the simultaneous clique savings. The required lower bound including the twelve anchor incidences and four ear incidences is 34,307,977. The contradiction has margin 5,871. All integer tables are verified by Lean's kernel. [Anchor score bounds](AnchorScores.lean) · [Rank estimate](ReservedRanks.lean) · [Final contradiction](IndependentThirteen.lean)

## Twelve-contact example

The explicit connected 33-vertex graph in TwelveWitness has 31 distinct triangle counts and 32 vertices of degree at least two. Its three degree-two vertices 29, 30 and 31 have respective neighbor sets {1,4}, {2,3} and {9,10}. The sole common neighbor of 9 and 10 is 31, and the leaf 32 is attached to 9. At h = 12 the anchors have five and six high exterior neighbors and attain triangle counts 11 and 16. The six ear neighbors are all distinct. Thus distinctness of the counts, independence of the ears, and the leaf attachment permit both anchor score bounds to be attained simultaneously at this next boundary. The set {1,2,3,4,9,10,14,15,17,18,32} 2-dominates this graph. The certificate gives an upper bound of 11 without requiring optimality. The graph was found by a targeted search. The formal proof checks its adjacency masks, connectivity, degrees, scores and dominating set directly. No enumeration completeness is claimed. The general independent case h ≤ 12 remains open in this work. [Checked graph and witness](TwelveWitness.lean)

## Source and replay map

| New module | Prior inputs or output |
| --- | --- |
| SimplicialTrial | Extends Joint17.trial in JointEarSample using the clique-neighborhood degree inequality in CliqueChoice384b and the deficiency fiber from FiniteRange384b. |
| SimplicialRanks | Combines the simultaneous saving with the sampling and rank infrastructure of JointEarRank. Proves the nine-draw estimate and the mass estimate used with ten draws. |
| IndependentFrontier | Uses Cover31.residual, Repair.maximal_diversity, PortRepair29.thin_degrees and the nine-draw inequality to obtain the 14-contact theorem and the necessary pool geometry at thirteen. |
| ReservedRanks | Uses the frozen credited-fiber bound in CreditRanks31 and rank ordering from JointRank to account for the two excluded anchor scores. |
| AnchorScores | Splits each anchor link into its exterior and its one possible ear edge using the edge representation from Repair384b. |
| IndependentThirteen | Combines the geometric and rank estimates into the direct catalogue theorem. |
| TwelveWitness | Adapts the frozen finite graph certificate in JointEarWitness to new adjacency masks and a new explicit 2-dominating set. |

The frozen predecessor archive has SHA-256 `9d48b8f73ae4711ccc7cdc60d781bbb7106f7fdd53eb3b478d9afb18bc310b3e`. It includes 254 graph modules and 615 checked axiom reports, with the previous weighted and joint-ear releases. Its JointEarSample, JointEarRank and JointEarWitness files were compared byte-for-byte with the public repository. The separate pendant-triangle branch plays no role in the independent-ear proof. [Published baseline manifest](https://github.com/vjdad4m/maths/blob/main/graffiti-384b-joint17/NEW-SOURCES.sha256)

Use Lean 4.19.0 at commit 6caaee842e94 and built Mathlib v4.19.0 at c44e0c8ee63ca166450922a373c7409c5d26b00b. Extract the package, enter graff384b-simplicial16 and run

```bash
CROSSFOUR_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin \
CROSSFOUR_MATHLIB=/absolute/path/to/mathlib4-4.19.0 \
bash replay.sh --cold
```

The recorded complete entry point used `--checked-249 /absolute/path/to/Strict249.log /absolute/path/to/Strict166.log`. It reused the archived 249-module baseline, rebuilt two weighted and three joint-ear modules, and compiled all seven modules in this extension. The cumulative chain has 261 graph modules and 629 axiom reports. Warnings are errors. Each of the fourteen new public theorems has a checked axiom report allowing only propext, Classical.choice, and Quot.sound. The optional `--checked-base /absolute/path/to/Strict166.log` rebuilds the last 95 modules.

[Strict transcript](Strict261.log) · [New source hashes](NEW-SOURCES.sha256) · [All source hashes](SOURCES.sha256) · [Delivery hashes](DELIVERY.sha256)
