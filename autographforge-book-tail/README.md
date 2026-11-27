# Three Slater-number bounds fail on a book with a pendant path

Take three triangles with a common edge, and attach a six-edge path to one endpoint of that edge. The resulting 11-vertex graph is connected, planar, chordal and $K_4$-free. Its Slater number is 2, its radius is 4, and its diameter is 7. It refutes the following three normalized AutoGraphForge conjectures. Every row assumes a finite simple graph with at least two vertices. [Standalone Lean source](BookTail.lean) · [Ján Pastorek’s catalogue](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt)

| Normalized / raw | Stable ID | Additional source hypotheses | Claimed bound | Witness |
|---|---|---|---|---|
| [187](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L187) / 192 | `7ca1b1ab` | chordal and planar | $\operatorname{rad}(G)\leq 2\,\mathrm{sl}(G)-1$ | $4>3$ |
| [221](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L221) / 231 | `0b4cc223` | chordal and planar | $\operatorname{diam}(G)\leq 4\,\mathrm{sl}(G)-2$ | $7>6$ |
| [877](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L877) / 926 | `a2ea93c1` | $K_4$-free and chordal | $\operatorname{rad}(G)\leq\tfrac32\,\mathrm{sl}(G)$ | $4>3$ |

## Witness and proof

Label the common edge $01$ and the three remaining triangle vertices $2,3,4$. The pendant path has labels $0,5,6,7,8,9,10$. The two largest degrees are 5 and 4. For the Slater number the first degree plus one reaches only 6, while the first two degrees plus two reach 11 exactly.

A shortest path from vertex 1 to vertex 10 has seven edges. It follows that the radius is at least four. Vertex 7 is within four edges of every vertex. In Lean, `metric_certificate` checks the entire distance table by two conditions. An edge increases distance from a fixed source by at most one. Every positive table entry has a neighbor one unit nearer the source. These conditions give the lower bound on every walk and construct a walk attaining each entry. Maximizing and minimizing the resulting eccentricities gives the exact diameter and radius.

Eliminate vertices in decreasing order of label. At each step the remaining neighbors of the current vertex form a clique. In an induced cycle of length at least four, the first cycle vertex eliminated would have two surviving cycle neighbors that must be nonadjacent, a contradiction. Lean formalizes this implication for an arbitrary graph in `chordal_of_elimination`. A direct four-vertex check certifies the absence of $K_4$.

For the planar embedding put vertices 0 and 1 at $(0,0)$ and $(12,0)$, and put each triangle vertex $v$ at $(6,v^2)$. Put path vertex $v=4+j$ at $(-j,100j^2+17j)$. Lean realizes each edge as an embedded real segment. It checks distinct vertex positions, avoidance of other vertices, agreement of the two orientations, and disjoint interiors for distinct edges.

The AutoGraphForge radius and diameter wrappers return positive infinity on disconnected inputs. GraphCalc's public functions call NetworkX directly. The Lean statements use extended rational distances for the source comparison, and the witness satisfies connectedness separately. The implementation replay checks the finite values with both upstream implementations and checks the catalogue's infinity convention on a disconnected test graph. [Catalogue wrappers](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/graphs/invariants.py#L269-L285) · [GraphCalc distance entry points](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py#L1045-L1097) · [Slater exporter](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/lean_project/LeanProject/GraphInvariants.lean#L61-L72)

## Reuse and prior work

The proof adapts the forbidden-induced-cycle definition used for the complete-graph witnesses, the eccentricity and radius definitions from the balanced-biclique proofs, the four-clique check from the diamond-ring work, and the plane-drawing construction from the planar and star certificates. The Slater definition agrees with the one used for row 33. The new proof reuses these definitions directly so the Lean file can travel on its own. [Balanced-forcing source](https://github.com/vjdad4m/maths/blob/72432ca314d9c196cd5480d60c1ffbb8bd174454/autographforge-balanced-forcing/BalancedForcing.lean) · [Published planar drawing definition](https://github.com/vjdad4m/maths/blob/72432ca314d9c196cd5480d60c1ffbb8bd174454/autographforge-303/AutoGraphForgePlanar.lean)

On November 27, 2026, upstream main was at `4d1a8afc99447cacd2328cca20e47b6493e8dbc5`. All three records were proposed and classified as `promising:class`. The release audit had no known or subsuming theorem for these records. The three statements and IDs were absent from the release refutations, and none of the IDs appeared in the released verified Lean proofs. The shared index at `72432ca314d9c196cd5480d60c1ffbb8bd174454`, upstream public issues and targeted searches for the IDs and inequalities yielded no earlier row-specific resolution. Gentner and Rautenbach study the Slater number in sparse and outerplanar graphs, with domination bounds that concern a different invariant. The chordal elimination criterion is classical. This search does not establish priority. [Release audit](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/audit_top_normalised.json) · [Shared result index](https://github.com/vjdad4m/maths/blob/72432ca314d9c196cd5480d60c1ffbb8bd174454/README.md) · [Upstream issues](https://github.com/JanPastorek/AutoGraphForge/issues) · [Gentner and Rautenbach](https://arxiv.org/abs/1608.04560)

## Replay

For Lean replay, set `MATHLIB_DIR` to a built Mathlib checkout at commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`, set `LEAN_BIN_DIR` to the
Lean 4.19.0 binary directory, and run `bash verify.sh`. The script checks
the pins and treats warnings as errors.

For the independent implementation check, put GraphCalc at
`ce66ac7390d945885e33f372e29c896fa32e9bc4` on the Python import path,
install its dependencies, and run
`python check-source.py /path/to/pinned/AutoGraphForge`.
