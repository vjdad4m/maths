# Graffiti.pc #199: deriving paired-high separation

In the covered four-block layout at orders 15 and 16, Lean derives
paired-high separation from singleton-high separation, the canonical
degree conditions, connectedness, and an induced-tree bound of five.
The combined theorem
`traceable_at_fifteen_or_sixteen_of_singleton_separation` therefore
does not assume paired-high separation in addition to those conditions.

The combined traceability theorem **still assumes no independent six-set**.
A separate checked family in `IndependenceObstruction.lean` shows why
that hypothesis cannot be dropped by a direct implication from the
catalogue's numerical conditions: both orders admit connected graphs
of connectivity three and induced-tree number at most five that do have
an independent six-set. These examples do not disprove #199.

What remains is to derive the covered four-block layout and singleton-high
separation from a minimum counterexample and to address the independent-six
branch. The full conjecture is not resolved.

Use Lean 4.19.0 and Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`
on `LEAN_PATH`. Run `bash graffiti-199-pair-separation/replay.sh` from the
repo root.
