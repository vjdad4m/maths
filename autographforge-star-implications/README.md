# AutoGraphForge star implications

The previously certified [star K₁,₁₆](../autographforge-star/StarCone.lean)
has zero forcing number 15 and two-forcing number 14. It is a tree and its
center with any three leaves induces a claw. The existing proof of row 2417
also provides the restrained-domination comparison.

| Physical row | Claimed consequent | Lean disproof |
| --- | --- | --- |
| [2900](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2900) | Not a tree | The threshold for two-forcing is 166/12 < 14. |
| [2901](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2901) | Not a tree | Directly transfers the prior row 2417 disproof by contraposition. |
| [2918](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L2918) | Claw-free | The threshold for two-forcing is exactly 14. |
| [6567](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L6567) | Claw-free | The strict upper threshold for zero forcing is 167/11 > 15. |
| [6613](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L6613) | Claw-free | Algebraically equivalent to row 2918. |

The exact rows were not indexed in the shared repo or listed in the
inspected upstream refutation or released Lean files. These are literal
catalogue certificates, not claims of novelty or of five independent results.

Replay from the repository with Lean and the built Mathlib 4.19.0 revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b`:
`MATHLIB_DIR=/path/to/mathlib4 bash replay.sh`.
