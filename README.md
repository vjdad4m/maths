# maths

Mathematical results, proofs, and reproducible verification.

## Results

- [Graffiti.pc Conjecture 108: counterexample](graffiti-108/README.md). The 35-vertex Kneser graph KG(7,3) makes the proposed inequality read **15 ≤ 13**. Includes a short proof, Lean verification, and an independent Python checker.

- [Graffiti.pc Conjecture 161: Lean formalization](graffiti-161/README.md). A star-extension proof of the proper-clique bound, with no novelty claim.

- [Graffiti.pc Conjectures 258 and 259: proofs](graffiti-258-259/README.md). Full written proofs, Lean-checked arithmetic and parity lemmas, and an exhaustive check through nine vertices.

- [Graffiti.pc Conjecture 261: proof](graffiti-261/README.md). A proof via Karpov’s spanning-tree theorem, with Lean-checked arithmetic and an exhaustive check through nine vertices.

## 20-conjecture batch

The 20 individual commits below contain written results (16 proofs and four counterexamples) for public review. Existing spot checks are labeled in the individual folders. **Full Lean formalization is in progress and only an end-to-end, verified Lean theorem qualifies as accepted.** No priority claim is made.

| Source | Conjecture | Outcome | Main argument or witness | Commit |
|---|---:|---|---|---|
| Graffiti.pc | [76](graffiti-76/README.md) | False | A 225-vertex triangle-free graph has largest induced tree 108, below 225/2. | [`e162661`](https://github.com/vjdad4m/maths/commit/e162661debcf6ebbb3a4db48766b8c08d7298e78) |
| Graffiti.pc | [157](graffiti-157/README.md) | True | A breadth-first tree makes the outer distance layer into leaves. | [`05dc3e4`](https://github.com/vjdad4m/maths/commit/05dc3e4f961274a466a08dc6823a0bc0bb117f12) |
| Graffiti.pc | [232](graffiti-232/README.md) | True | A three-point projection onto a diameter path of the connected dominating tree. | [`f031114`](https://github.com/vjdad4m/maths/commit/f031114f59e1650e9413ae2161b7c9d0dacb5008) |
| Graffiti.pc | [235](graffiti-235/README.md) | True | Deduction from Henning–Yeo plus a bipartite dominating-edge argument. | [`e8a92b5`](https://github.com/vjdad4m/maths/commit/e8a92b59c50ecaf168bde058fa51d54d58515b19) |
| Graffiti.pc | [255](graffiti-255/README.md) | False | A checkerboard-colored 8×8 rook graph plus a three-vertex path gives 126 < 134. | [`bdb0db4`](https://github.com/vjdad4m/maths/commit/bdb0db4992cd3c894ad0b31ddeac8fb960b75164) |
| Graffiti.pc | [260](graffiti-260/README.md) | True | Count both the periphery and its boundary when the max leaf count is three. | [`65e8ec0`](https://github.com/vjdad4m/maths/commit/65e8ec039ebb9b0ff9352e2ecbbd5ee02b138c6f) |
| Graffiti.pc | [271](graffiti-271/README.md) | True | Diameter bound; a dominating edge separately handles total domination two. | [`de2dd79`](https://github.com/vjdad4m/maths/commit/de2dd7919f4d870b1d33e08ab45deb8ed66d74e3) |
| Graffiti.pc | [310](graffiti-310/README.md) | True | Charge depths in a breadth-first tree. | [`7e3ed45`](https://github.com/vjdad4m/maths/commit/7e3ed45f86414b8eb3aa5f69fd7a2f223ec01cc5) |
| Graffiti.pc | [361](graffiti-361/README.md) | True | All supports are forced; two centers preclude the tight single-extra case. | [`58ad4db`](https://github.com/vjdad4m/maths/commit/58ad4db78e23f6079387eda1651d2183df22caa3) |
| Graffiti.pc | [362](graffiti-362/README.md) | True | Reserve one support per component; remaining vertices distance-two dominate. | [`e186f9f`](https://github.com/vjdad4m/maths/commit/e186f9fb43472012b6fccf6abff5e5488845d91f) |
| Graffiti.pc | [381](graffiti-381/README.md) | True | Distribute isolates of the support neighborhood among isolated supports. | [`d5ac6a3`](https://github.com/vjdad4m/maths/commit/d5ac6a3192a7798afed2864b1d59000379371d74) |
| Graffiti.pc | [416](graffiti-416/README.md) | True | In diameter two, a pendant's neighbor is universal. | [`1907180`](https://github.com/vjdad4m/maths/commit/19071800a990bf219cbc44c1da08609e49eee3ce) |
| Graffiti.pc | [426](graffiti-426/README.md) | True | Seed a maximal independent set to avoid isolates of the induced neighborhood. | [`2ae46ef`](https://github.com/vjdad4m/maths/commit/2ae46ef7517da2d541d75ec4edf0f4bcf014a27c) |
| Graffiti.pc | [444](graffiti-444/README.md) | False | 34 vertices induce a matching plus isolates, exceeding the bound of 33. | [`5daf5b6`](https://github.com/vjdad4m/maths/commit/5daf5b661ecf9e35d615e5aa597a571d4f8f9679) |
| Graffiti.pc | [446](graffiti-446/README.md) | True | Charge selected supports to excluded private leaves or count them directly. | [`604135a`](https://github.com/vjdad4m/maths/commit/604135acc3712735b2adadcc117ca6c9ee87726b) |
| Graffiti.pc | [448a](graffiti-448a/README.md) | True | Count low-degree runs in a path cover. | [`1f240d6`](https://github.com/vjdad4m/maths/commit/1f240d6adf8efcd091b3223f1902e0d2334938eb) |
| Graffiti.pc | [449](graffiti-449/README.md) | True | Count edges leaving the high-degree part of a 2-independent set. Uses the catalogue's ceiling. | [`745449c`](https://github.com/vjdad4m/maths/commit/745449c494734871acc5f9a45def1bf6b6e41ba8) |
| Graffiti.pc | [450](graffiti-450/README.md) | True | Charge selected supports to private neighbors or discarded low-degree vertices. | [`670a91d`](https://github.com/vjdad4m/maths/commit/670a91ddf81d9fcffa13e2f50d28c3d7b9d645ee) |
| Davila Graffiti³ | [14](graffiti3-14/README.md) | True, sharp | Prime-factor bounds reduce Euler's totient inequality to 45 exact cases. | [`9badedf`](https://github.com/vjdad4m/maths/commit/9badedfb7ca95d96da318c50c21c51e25d68fc73) |
| Davila Graffiti³ | [27](graffiti3-27/README.md) | False | An order-64 dihedral group gives 19 classes against a claimed lower bound of 89/4. | [`c049141`](https://github.com/vjdad4m/maths/commit/c04914102da94a87e19b357fa0f187dd3a04d0fc) |
