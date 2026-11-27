# Ear endpoints of degree four in Graffiti.pc #384b

**At order 33 and diversity 33, the entire degree-four ear endpoint case satisfies the catalogue bound for every attachment of the deleted vertex.** In the normalized core, deleting the leaf gives a 32-vertex graph H with positive pairwise distinct vertex triangle counts and a five-clique. If a degree-two ear e has adjacent neighbors a,c and either endpoint has degree at most four, then γ₂(H) ≤ 15. Adding the deleted vertex gives γ₂(G) ≤ 16. The lifting theorem also permits an arbitrary deleted vertex with this core. [Core and full-graph statements](PaletteFinish33.lean)

Here γ₂ is the minimum size of a set supplying at least two neighbors to each vertex outside it. Diversity is the number of distinct vertex triangle-incidence counts, including zero whenever realized. For 33 vertices and 33 types, the catalogue expression ⌊n − |T|/2⌋ is 16. All structural degrees and counts below refer to H.

## A further restriction at higher degree

Suppose s,t are distinct common neighbors of a,c other than the ear. If any of a,c,s,t has triangle count four or five, then γ₂(H) ≤ 15. This result requires order 32 and positive distinct counts. The five-clique existence assumption is unnecessary for this inequality. In the normalized extremal core with a five-clique and γ₂(H) ≥ 16, both endpoints and **every** additional common neighbor must therefore have triangle count at least six whenever there are at least two additional common neighbors. The previously checked lower bound of four for each of those counts excludes the values below four. [Shared-neighbor theorem, six-triangle bound and full-graph lift](PaletteFinish33.lean)

Every order-32 extremal core in the leaf-and-ear reduction now has both ear endpoints of degree at least five. The larger-ear case is open. In particular, the preceding release leaves a cubic-root case with the ear as the only common neighbor and at least one endpoint of degree six or more. This release gives no closure for that case or for lower diversity.

## Proof

1. **Every five-clique meets the endpoint pair when s and t exist.** Consider a five-clique C and two disjoint sets of pins whose union contains e. Each pinned vertex has two neighbors in the opposite set. If the pins meet C only at q, the earlier cut theorem gives two cubic vertices covering the other four members, each seeing two of those four. The covering cubics can be chosen with at most two neighbors in C. Four clique vertices must be covered, hence both cubics have that upper bound, and neither is adjacent to q. Thus q is exactly the vertex of C without a cubic neighbor. If a,c both missed C, the ear-square through s and the ear-square through t would give two different choices for this uniquely determined q. This contradiction proves the claim under the half-order obstruction. [Unique contact](PaletteContact33.lean)
2. **Retain a and c.** The vertices e,s,t already have two retained neighbors. Choose ten vertices from W = V(H) ∖ {e,a,c}, which has size 29. Test the 27 vertices of U = W ∖ {s,t}. Add each unselected test vertex with fewer than two neighbors in the retained set and the sample. This always yields a 2-dominating set. The target requires a sample with at most three additions. [Construction](PaletteSample33.lean)
3. **Count the deficient samples at each vertex.** A test vertex adjacent to neither retained endpoint has the same triangle count and degree after both are deleted. Every five-clique meets the endpoint pair, so the deletion is five-clique-free. Turán's bound in the neighborhood gives the upper bound on the triangle count at a given degree. A test vertex adjacent to exactly one retained endpoint only fails on samples that avoid it and all its neighbors in W. For two retained neighbors its failure count is zero. [Local Turán bound and sample counts](PaletteFibers33.lean)
4. **Sum over distinct triangle counts.** The 27 test vertices have distinct counts at least two. A count of four or five is already occupied by one of a,c,s,t and absent from U. After omitting that value, the rank of each vertex bounds its minimum count, hence its maximum number of deficient samples. Lean verifies the total upper bound **80,087,034**. Four deficiencies in each sample would require at least 4 × binom(29,10) = **80,120,040**. The difference of 33,006 gives a sample with at most three additions and a set of size at most 2 + 10 + 3 = 15. [Exact integer table](PaletteFibers33.lean) · [Double count](PaletteSample33.lean)
5. **Apply this to degree four.** Earlier checked results exclude a cubic endpoint in an extremal core. For a degree-four endpoint the thin case already gives a strict saving. In the remaining case, its two exterior neighbors are the common neighbors s,t and that endpoint has triangle count four. Step 4 applies for every leaf root. [Final implication](PaletteFinish33.lean)

## Replay map

| New module | Direct import | Reused results |
| --- | --- | --- |
| PaletteContact33 | HighEarRootCap33 from the preceding release | EarFrame33.cover, EarAttachment33.frame_obstruction and common_neighbor, CubicShore.square_frame |
| PaletteFibers33 | PaletteContact33 | EarPrune.lost_score, EarAnchor.induced_degree, RankTuran.local_turan, RankTable.cap_table, FiniteRange.count_bad |
| PaletteSample33 | PaletteFibers33 | JointRank.rank_lower and sum_by_rank, FiniteRange.bad, EarAnchor.outside |
| PaletteFinish33 | PaletteSample33 | HighEar.four_endpoint and thin_four_below_half, CubicShore.endpoints and square_profile, EarAnchor.gamma_induced_iff |

The public cut and local clique results concern the same finite simple-graph invariants as the imported files. The #299 transversal estimate and #397c domination lift do not supply the clique-contact or deficiency-count conclusions required here. The proof uses finite arithmetic on ranks and degrees. It assumes no external graph census. [Shared result index](https://github.com/vjdad4m/maths/blob/main/README.md) · [Published pinned cut](https://github.com/vjdad4m/maths/blob/main/graffiti-384b-ear-exchange/EarFrame33.lean) · [Published frame overlap](https://github.com/vjdad4m/maths/blob/main/graffiti-384b-ear-exchange/EarAttachment33.lean)

From the repository root, with Lean and a built Mathlib v4.19.0 checkout:

```bash
CROSSFOUR_LEAN_BIN=/absolute/path/to/lean/bin \
CROSSFOUR_MATHLIB=/absolute/path/to/mathlib4 \
bash graffiti-384b-ear-palette/replay.sh
```

The original [strict transcript](Strict194.log) rebuilt all four modules and checked every printed axiom report against the standard whitelist. Their [source hashes](NEW-SOURCES.sha256) are included.
