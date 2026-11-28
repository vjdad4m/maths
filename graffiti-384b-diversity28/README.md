# Graffiti.pc #384b with exactly 28 triangle-count types

**Every finite simple graph on n vertices with exactly 28 distinct vertex triangle counts has a two-dominating set of size at most n − 14.** The triangle count at a vertex is the number of unordered triangles containing it. Zero is a type when some vertex realizes it. Every vertex outside the two-dominating set has two distinct neighbors in it. The theorem applies to disconnected graphs as well. The general conjecture remains open. [Bound and existence theorem](DiversityTwentyEight384b.lean)

## Proof

Let H be the set of vertices of degree at least three, and call vertices of degree two ears. The published even-diversity lifting theorem covers graphs with fewer than 28 nonleaves. With at least 28 nonleaves, a hypothetical failure has exactly 26 vertices in H. Indeed, the number of types is at most |H| + 2, and a maximum cut gives at least ⌈|H|/2⌉ feasible omissions. Equality in the type count forces the 26 counts on H to be distinct and at least two. There are at least two ears. [Original-graph reduction](DiversityTwentyEight384b.lean) · [Even-diversity lifting theorem](https://github.com/vjdad4m/maths/blob/main/graffiti-384b-diversity30/EvenNonleaves384b.lean)

Sample ten vertices uniformly from H and initially retain all vertices outside H. Fix any independent set E of ears. Omit each ear in E whose high-degree neighbors were all sampled. Each eligible ear keeps its two neighbors, and no unsampled high vertex loses a retained neighbor. Also omit each sampled vertex whose neighborhood is a clique and which has two retained neighbors. A high vertex with a clique neighborhood can only have neighbors of at least its own degree, so deleting ears preserves this second set of omissions. The frozen simultaneous-removal lemma then allows the remaining deficient vertices to be added. [Ear eligibility and double count](EarCredit28.lean) · [Compatible clique-neighborhood removals](prior/SimplicialCredit30.lean)

For a vertex at zero-based triangle-count rank r in H, its count is at least r + 2. Its degree d therefore satisfies r + 2 ≤ C(d, 2). When equality holds and the vertex attains C(d, 2), its neighborhood is a clique. Counting samples which contain the vertex and give it two retained neighbors supplies an additional saving at that rank. A high vertex adjacent to an ear already has one retained neighbor in every sample where the high vertex is unsampled. It also cannot have a clique neighborhood. These two facts lower the charge at each distinct such high vertex by at least 170,170. The rank estimates sum to 17,881,977. The proof caps the degree parameter at 11 and checks every permitted combination of rank and capped degree in Lean. [Rank table and graph coverage](TenSeeds28.lean)

If the graph fails, it admits at most 13 omissions. Before repairs, each sample leaves 16 unsampled high vertices. Across the C(26, 10) samples that forces 15,935,205 repair incidences, plus every additional omission. Write M for the number of distinct high vertices adjacent to an ear and a(e) for the number of high neighbors of ear e. Subtracting the compulsory repair incidences from the rank total gives

```text
sum over e in E of C(26 − a(e), 10 − a(e)) + 170,170 M ≤ 1,946,772.
```

The inequality applies to every independent family E of degree-two vertices, even when the graph contains more ears. [Budget theorem](RankBudgetTypes28.lean)

* If any ear has at most one high neighbor, take that ear alone. Its contribution is at least C(25, 9) = 2,042,975, exceeding the budget by **96,203**.
* Otherwise every ear has two high neighbors, so all ears are independent. Choose two. If their combined high neighborhood has at most two vertices, the existing low-support maximum-cut theorem gives the 14 desired omissions directly. Otherwise M ≥ 3. The two ears and three distinct neighbors contribute at least 2 C(24, 8) + 3 · 170,170 = 1,981,452, exceeding the budget by **34,680**. [Both cases in Lean](DiversityTwentyEight384b.lean)

## Source and replay map

The four linked top-level Lean files constitute the extension. It reuses the exact catalogue definitions, `exact_of_high`, `Repair.maximal_diversity`, `Repair.exact_of_low_support`, `JointRank.rank_lower`, `BoundaryFiber.count`, and `EarMix.clean` and `active_fiber`. The public diversity-30 theorem supplies its general even lifting lemma. The diversity-29 rooted equality requires odd diversity. The published discounted-repair maximum cut requires information about adjacency among deficient vertices. Here the fixed degree-two neighbors and sampled clique neighborhoods give sufficient savings with all deficient vertices added. [Public index](https://github.com/vjdad4m/maths/blob/main/README.md) · [Odd-diversity hypothesis](https://github.com/vjdad4m/maths/blob/main/graffiti-384b-diversity29/OddQuota384b.lean) · [Discounted-repair theorem](https://github.com/vjdad4m/maths/blob/main/graffiti-384b-discounted-repairs/MaxRepair.lean)

The source archive includes the exact transitive closure of 305 predecessor Lean files under `prior/`. Their source and object hashes were authenticated against the frozen six-anchor release, whose source archive has SHA-256 `e8216c4c7f864e4c70d68959254d1894cd14d941bb61c66f67a3849147aebc74`. The proof uses no external enumeration. [New sources](NEW-SOURCES.sha256) · [Predecessor sources](PRIOR-SOURCES.sha256) · [Predecessor object paths and hashes](CHECKED-OBJECTS.tsv) · [New objects](NEW-OBJECTS.sha256)

The two recorded replays used the working sources and an independently unpacked copy. Each authenticated 305 predecessor objects, recompiled all four new modules, matched their object hashes, and checked seven axiom reports. The runner scans all 309 project sources for proof placeholders, custom axiom declarations and native_decide. The axiom allowlist contains propext, Classical.choice and Quot.sound. Lean runs with warnings as errors, synchronous elaboration, and one thread. The pinned versions are Lean 4.19.0 at 6caaee842e94 and Mathlib v4.19.0 at c44e0c8ee63ca166450922a373c7409c5d26b00b. [Replay entry point](replay.py)

From the unpacked source directory, use the first command with the recorded predecessor objects. The second rebuilds every project predecessor from the bundled sources. Set CROSSFOUR_LEAN_BIN and CROSSFOUR_MATHLIB to your local Lean binary directory and Mathlib checkout if needed. The recorded runs used checked mode.

~~~sh
python3 -B replay.py --checked /absolute/path/to/shared/workspace
python3 -B replay.py --cold
~~~
