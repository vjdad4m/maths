# AutoGraphForge cycle implications

The 43-cycle is subcubic and 2-regular. The existing [Lean cycle package](../autographforge-1130/)
checks burning number 7, vertex clique cover number 22, and outer-connected
domination number 41. Specializing those exact values refutes the following
physical lines of the pinned survivor list:

| Row | Claimed consequent | Failed test on the witness |
| --- | --- | --- |
| [3378](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L3378) | Not subcubic | 3·7−2 < 22 |
| [4293](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L4293) | Not subcubic | 7 < 22/3+2/3 |
| [4298](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch_normalised.txt#L4298) | Not regular | 7 < 41/6+5/3 |

Rows 3378 and 4293 are algebraically equivalent, hence these are two distinct
refutations. Lean quantifies over defined numerical values of the optional
outer-connected domination invariant. The exact rows were absent from the
inspected upstream refutation files and released Lean sources. This is
explicit certification of existing witness calculations on new rows, not
a claim that the upstream graph corpus contained no implicit witness.

Replay from the repository with Lean and the built Mathlib 4.19.0 revision
`c44e0c8ee63ca166450922a373c7409c5d26b00b`:
`MATHLIB_DIR=/path/to/mathlib4 bash replay.sh`.
