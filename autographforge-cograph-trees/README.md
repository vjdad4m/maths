# AutoGraphForge: the cograph-tree star profile

One Lean theorem proves seventeen physical catalogue rows. Every nontrivial cograph tree is a star, including the two-vertex case. If the star has **m** leaves, its size, maximum degree, independence number, edge-cover number, annihilation number, Havel–Hakimi residue, and outer-connected domination number all equal **m**.

## Why the reduction works

The [proper-join theorem from row 534](../autographforge-534/CographJoin.lean) splits any connected nontrivial cograph into two nonempty shores, with every cross edge present. If both shores had two vertices, the cross edges would give a four-cycle, so one shore is a singleton. An edge on the other shore would give a triangle through the singleton. Thus the only edges are the spokes.

All leaves form a maximum independent set and cover every outer-domination requirement while leaving the center connected by itself. [Row 370’s forest lemma](../autographforge-370/OuterForest.lean) already bounds outer-connected domination below by independence. Every edge cover must use the unique spoke at each leaf. The ascending list of degrees is m ones followed by m, so exactly m entries fit the edge budget. Descending Havel–Hakimi, using [Graffiti.pc #324’s implementation](../graffiti-324/Proof324.lean), removes m and reduces all remaining degrees to zero in one step.

- [StarStructure.lean](StarStructure.lean): structural reduction.
- [StarNumbers.lean](StarNumbers.lean): invariant calculations.
- [Rows.lean](Rows.lean): combined profile and the seventeen exact catalogue consequences.

| Physical row | Stable ID |
|---:|---|
| [1173](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1173) | `e7096118` |
| [1178](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1178) | `b729e642` |
| [1181](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1181) | `311b1ac4` |
| [1212](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1212) | `1ac11681` |
| [1215](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1215) | `5702c370` |
| [1227](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1227) | `b9bc4932` |
| [1229](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1229) | `07397072` |
| [1257](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1257) | `86a94892` |
| [1272](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1272) | `a4a3d46a` |
| [1314](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1314) | `9d01e7ae` |
| [1316](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1316) | `dc5ea2c2` |
| [1415](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1415) | `470e4b4c` |
| [1416](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1416) | `7c42cecc` |
| [1638](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1638) | `1cad9201` |
| [1640](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1640) | `56cfadea` |
| [1643](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1643) | `e661c780` |
| [1644](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L1644) | `9ac8d097` |

These are consequences of one structural theorem, not seventeen independent discoveries. In the pinned release each exact entry was marked proposed, with no Lean proof recorded; no matching statement or ID was found in the inspected refutation or released Lean files. The outer-connected domination result also proves existence of a numeric value, rather than assuming the invariant is defined.

## Replay

Run with Lean 4.19.0 and built Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`:

```bash
MATHLIB_DIR=/absolute/path/to/mathlib4 bash autographforge-cograph-trees/replay.sh
```

Replay compiles from source with warnings as errors and checks that every exported row uses only `propext`, `Classical.choice`, and `Quot.sound`.
