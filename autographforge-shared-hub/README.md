# Three AutoGraphForge counterexamples on one graph

Identify one degree-ten hub of the complete bipartite graph $K_{2,10}$ with vertex 0 of a 12-cycle. The resulting graph has 23 vertices, Slater number 2, burning number 4 and diameter 8. Lean proves each invariant value and refutes all three rows. The table uses physical line numbers in Ján Pastorek's normalized survivor file at commit `4d1a8afc99447cacd2328cca20e47b6493e8dbc5`.

| Physical row | Generated ID | Catalogue hypotheses | Proposed inequality | Witness |
|---:|---|---|---|---|
| [747](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L747) | `f5fb63cd` | Nontrivial, Eulerian, triangle-free | $b ≤ 3s/2$ | $4>3$ |
| [1889](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1889) | `b9676bdc` | Nontrivial, Eulerian, triangle-free | $b ≤ s/3+3$ | $4>11/3$ |
| [2517](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2517) | `79f1b599` | Nontrivial | $d ≤ 14s/5+7/5$ | $8>7$ |

Here $s$ is the Slater number, $b$ is the burning number and $d$ is the diameter. GraphCalc calls a graph nontrivial when its order is at least two. Its diameter routine calls NetworkX and requires connectivity for a numerical value. AutoGraphForge’s separate diameter wrapper represents disconnected inputs by positive infinity. Lean refutes the row both under that unrestricted wrapper and after restricting to connected inputs with finite diameter. [AutoGraphForge diameter wrapper](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/graphs/invariants.py#L269-L275)

## Why the witness works

The shared hub has degree 12, the other hub degree 10 and every other vertex degree 2. The graph is connected, so all degrees being even makes it Eulerian. Identifying the two pieces at a single vertex preserves triangle-freeness. GraphCalc uses the least $t$ such that $t$ plus the sum of the $t$ largest degrees reaches the order. Here $1+12<23$ and $2+12+10≥23$, giving $s=2$. [GraphCalc graph classes and diameter](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/core/basics.py) · [Slater implementation](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/degree.py#L227-L358)

The cycle retains its usual shorter-arc distances. Every path from a vertex off the cycle to a cycle vertex passes through the shared hub. Consequently, a ball of radius $r$ about any vertex meets the cycle in at most $2r+1$ vertices. In three rounds, balls of radii 2, 1 and 0 cover at most nine of the twelve cycle vertices. In four rounds, the radius-three ball at the shared hub covers the entire bipartite piece and seven consecutive cycle vertices. The radius-two ball at its antipode covers the other five. The formal proof checks the ball bound for every radius and supplies a four-round schedule under GraphCalc's metric-cover formulation. The greatest distance is eight, from the other hub to that antipode. [GraphCalc burning model](https://github.com/RandyRDavila/GraphCalc/blob/ce66ac7390d945885e33f372e29c896fa32e9bc4/src/graphcalc/graphs/invariants/zero_forcing.py#L1437-L1512)

## Status, attribution and reuse

All three generated records had status `proposed` and null Lean proofs at the pin. Searches of the three release refutation JSON files, the two released verified proof files, the upstream issues and the public maths index found no exact row entry on 27 November 2026. The public upstream issue treats row 2596. [Generated records](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/cegis_results.json) · [Verified proofs](https://github.com/JanPastorek/AutoGraphForge/tree/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/verified_proofs) · [Upstream issue](https://github.com/JanPastorek/AutoGraphForge/issues/1) · [Maths index](https://github.com/vjdad4m/maths/blob/main/README.md)

**Row 2517 already follows from the published row 33 family.** The theorem `Lollipop.separation` supplies connected graphs of Slater number two and arbitrarily large burning number. Every connected graph satisfies $b≤d+1$, since a first ignition reaches all vertices within $d$ propagation rounds. Those graphs therefore have arbitrarily large diameter. The present artifact gives a small triangle-free Eulerian witness and an exact numerical certificate. The known lollipops contain triangles and do not furnish the witnesses for the two Eulerian triangle-free rows. [Published row 33 proof](https://github.com/vjdad4m/maths/blob/main/autographforge-33/Lollipop.lean)

The burning argument uses classical results about graph burning. Bonato, Janssen and Roshanbin gave the covering upper bound in Corollary 3, the external-ball condition for isometric subgraphs in Theorem 7 and the cycle formula in Corollary 11. The shared hub satisfies that external-ball condition. A search for earlier counterexamples combining burning number and Slater number on triangle-free Eulerian graphs found no exact prior resolution of rows 747 or 1889. [How to Burn a Graph](https://doi.org/10.1080/15427951.2015.1103339)

The standalone Lean file reuses the burning and Slater definitions from row 33 and the generic distance-certificate proof, Euler criterion and diameter definition from rows 501/764. The metric certificate verifies that distance vanishes exactly on equal vertices, changes by at most one across an edge, and admits a descending neighbor at every unequal pair. These checks connect the explicit distance formula to Mathlib's actual shortest-walk distance. [Rows 501/764 source](https://github.com/vjdad4m/maths/blob/main/autographforge-eulerian-chain/Chain.lean)

## Replay

The complete local Lean source is `SharedHub.lean`. With Lean 4.19.0 on PATH and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`, run from the source folder.

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash replay.sh
```

The script checks the pins, runs warnings as errors, and checks that the three invariant theorems and the three disproofs print only `propext`, `Classical.choice` and `Quot.sound`. To check the same graph separately with GraphCalc 2.0.0, NetworkX 3.5 and PuLP with CBC, run `python check_source.py`. It asserts all three strict inequalities with exact rational arithmetic.

