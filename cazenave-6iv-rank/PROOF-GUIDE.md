# Cazenave 6(iv), rank inequality

[Cazenave's source, arXiv:2611.03879v1](https://arxiv.org/abs/2611.03879v1), §7, Conjecture 6(iv), second inequality.

* **Main statement:** CazenaveRank.cazenave_six_iv_rank in Complete.lean.
* **Equality:** CazenaveRank.cazenave_six_iv_rank_equality in Complete.lean states equality iff the graph is of order two, i.e. K₂ under the connected hypothesis.
* **Exact definitions:** columnRank is the real dimension of the span of the adjacency-matrix columns. conventionalWeight is the reciprocal square root of the product of the endpoint degrees; the main statement uses the unordered-edge sum.
* **Written proof:** PAPER.md gives a short symbolic range argument and six remaining exact small comparisons. Run python3 verify_paper_intervals.py to replay the written proof's arithmetic.
* **Lean proof:** the large-order graph proof uses an adjacent permutation on a principal rank witness. The reduced small-order case uses 2,111 exact rational charging comparisons instead of formal differentiation. These are kernel-checked in SmallChunk0–8.lean and lifted to real inequalities in Small.lean. check_small.py is a readable duplicate checker, not a trusted input to Lean.

## Replay

Use Lean 4.19.0 (commit 6caaee842e94) with mathlib4 at c44e0c8ee63ca166450922a373c7409c5d26b00b. From an already built mathlib checkout at that revision, run:

~~~bash
lake env bash /absolute/path/to/this/folder/replay.sh
~~~

The script uses a fresh build directory for all proof modules and fails on warnings. For the main theorems, Lean reports only propext, Classical.choice, and Quot.sound.
