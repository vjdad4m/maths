# Graffiti.pc #384b and simultaneous five-point selection

In the exact profile there are 29 distinct vertex triangle counts, 29 vertices of degree at least two and 27 vertices of degree at least three. The two degree-two vertices are the ears. Their four distinct high neighbors are the anchors. The other 23 high vertices form the pool. Let T count the pool vertices on an anchor triangle, and let M count those with any neighbor outside the pool. The catalogue target in this profile is γ₂(G) ≤ |V(G)| − 15. [Official catalogue, Ermelinda DeLaViña](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/index.html) · [Catalogue data, entry 384b](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json)

The preceding proof showed that five pool vertices suffice if, after fixing the four anchors and the two ears, they retain two triangles at each anchor and thirteen at some anchor. It also proved the catalogue inequality at T ≤ 5 and whenever all four global anchor scores are at most twelve. The remaining range entering this proof was 6 ≤ T ≤ M ≤ 14. The present results give sufficient conditions throughout that range and a connected order-29 example that precludes an unconditional extension of the five-point test to T = 6.

## Common deletion

For any carrier of pool vertices, let s denote the triangle count of an anchor inside that carrier together with the six fixed vertices. The link graph of the anchor has s edges. Deleting a carrier vertex loses at most its degree in this link. For r nominated deletions, the sum of their degrees is at most s + C(r,2). An edge can contribute twice only if both its endpoints are nominated.

Consequently at most b vertices can make a score fall below d if, for r = b + 1,

```text
r·(s+1) > r·d + s + C(r,2).
```

Assign each anchor its own budget b. If the four budgets sum to less than the carrier size, some deletion preserves all four quotas. Repeating this step yields a common set of five points. [Link incidence and common deletion](ChoiceIncidence.lean) · [General thinning induction](ChoiceShrink.lean)

The following graph-level conditions imply the catalogue inequality. The rows also apply to any carrier of the indicated size inside a larger contact set, using the triangle counts inside that smaller carrier. When the carrier comprises all T contacts, its anchor counts are their original global counts.

| Carrier size | Minimum at one distinguished anchor | Minimum at each of the other three |
|---:|---:|---:|
| 6 | 20 | 4 |
| 7 | 28 | 8 |
| 8 | 37 | 16 |
| 9 | 47 | 32 |

At size n the three ordinary anchors each receive one veto and the distinguished anchor receives n−4. This leaves at least one common deletion. The proof uses the actual sets of spoiled choices only through an upper bound on their union. [Graph theorem for all triangle contacts](ChoiceShrink.lean) · [Embedding into the original graph](ChoicePatch.lean)

## Weighted choice for arbitrary T

Fix some pool vertices F, choose any pool subregion U, and draw k vertices from U with |F| + k ≤ 5. Write B for F together with the ears and anchors. For an anchor, each triangle with both partners in B ∪ U contributes C(|U|−j,k−j) to the sum of its scores over all draws, where j is the number of its partners outside B. The contribution is zero if j exceeds k. Thus the mean is computable from the three counts for j = 0, 1, 2.

If F already guarantees two triangles at the three ordinary anchors, a total exceeding 12·C(|U|,k) at the distinguished anchor gives a common successful draw. The simultaneous version also allows those other three anchors to depend on the draw. If N = C(|U|,k), s is the full carrier score, m the computed sum of scores, and d the desired quota, the number of bad draws is at most floor((sN−m)/(s−d+1)) when d ≤ s. It is zero if the fixed vertices already supply d, and always at most N. A sum of the four bounds smaller than N proves the catalogue inequality. No independence condition is imposed. [Extension counts](ChoiceMass.lean) · [Simultaneous graph theorem](ChoiceSimultaneous.lean)

## When five points cannot succeed

At an anchor exactly at its quota, every triangle partner outside the base is compulsory. Suppose an anchor has score two and forces two pool points R. At another anchor, charge the triangles using the first anchor, either ear or a point of R. All remaining triangles in a five-point selection must use their two other vertices from at most two other anchors and three freely selected points. They therefore number at most ten. If each other anchor has at most two charged triangles, none can reach thirteen. This obstruction applies at any T. [Compulsory partners](ChoiceTight.lean) · [Competition bound](ChoiceCompetition.lean)

The explicit connected graph on 29 vertices has 29 different triangle counts, 29 nonleaves, 27 high vertices and T = M = 6. Vertices 27 and 28 are the ears with neighbor pairs {0,1} and {2,3}. The four anchor counts in this order are **2, 13, 9, 6**. Vertex 0 requires contacts 4 and 5 to retain its two triangles. Vertex 1 requires 6, 7, 8 and 9 to retain its thirteen. In fact a selection passes the score test exactly when it contains all six contacts, even when other pool points can be chosen freely. [Adjacency matrix and score checks](SixObstructionData.lean) · [Exact minimum carrier](SixObstruction.lean)

On this graph any protected cut covering both ears needs a pin outside the twelve local vertices. Ear 27 forces both anchors 0 and 1 opposite it. To protect 0 a local cut would have to use 4 or 5 on the ear side. Each of 4 and 5 has just 0 and its mate as local neighbors, so protecting it forces 0 onto both sides. Exactly one outside pin suffices. The shores {0,1,10,28} and {2,3,5,7,27} work. More generally a protected frame carrying one ear can absorb the other ear when both of its anchors see the same available shore. The example also comes with an explicit 14-vertex two-dominating set. [Frame extension](ChoiceFrame.lean) · [Exact outside-pin minimum and 14-vertex certificate](SixObstruction.lean)

The remaining question is whether the domination bound holds for graphs in the residual profile that evade both the score conditions and the cut constructions.

## Source and replay

The source closure uses the five-contact package with SHA-256 `c6a5c6b13183952c9d4d50bd06575b69027c166db719e83c7fd4be5c174b1733`. Its protected-patch theorem, profile reductions, and induced-score embedding are used here. The hypergeometric calculation specializes `RankStrata.hits`. The finite example reuses the ordered-pair triangle counter from `FiveData.lean` in the four-contact archive (`22e5e701d1e366e2b24c1490ab880d18ebb1b558bd3eb8c763c70ba521aac9f9`) and adapts that package's private-triangle cut argument. The graph and its full score table are different. The five-contact predecessor in turn uses the published 30-nonleaf simultaneous-removal argument. [Published five-contact theorem](https://github.com/vjdad4m/maths/tree/17a1b014e1204d51985f6cba1cccb5b3b9050fe4/graffiti-384b-five-triangle-contacts) · [Published sampling predecessor](https://github.com/vjdad4m/maths/tree/b33aad93ffcaab8f8c9e21a6fc56592675782f6f/graffiti-384b-30-nonleaf-complete)

In the shared scratch folder run

```sh
python3 -B replay.py --checked ..
```

For a cold rebuild of all project modules from the extracted source archive, run

```sh
CHOICE_LEAN_BIN=/absolute/path/to/lean-4.19.0-linux/bin \
CHOICE_MATHLIB=/absolute/path/to/mathlib4-4.19.0 \
python3 -B replay.py --cold
```

The runner verifies Lean 4.19.0 commit `6caaee842e94` and Mathlib v4.19.0 commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. It checks the transitive source manifests, runs with warnings as errors and audits printed theorem axioms against `propext`, `Classical.choice` and `Quot.sound`. [Replay script](replay.py) · [Strict transcript](StrictChoice.log)

All ten new modules passed direct strict compilation. The packaged transcript checks all 31 printed axiom reports. An extracted replay independently reproduced 8 of the ten object digests. Every source file in the archive was matched to its checked worktree digest. The 351 predecessor objects were reused after hash checks. The cold replay option is supplied for independent use.

[Complete pinned Lean sources](proof-sources.zip). Extract the archive and use its replay script.
