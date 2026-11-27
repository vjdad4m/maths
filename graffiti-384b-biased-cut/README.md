# A degree-biased cut for Graffiti.pc #384b

This is a general structural lemma, not a proof of #384b. Maximize the integer objective 3|B|−2e(G[B]) over the retained set B. Every maximizer is 2-dominating and has induced maximum degree at most one. A vertex outside B with exactly two retained neighbors cannot meet two different retained matching edges. Exchanging such an outside vertex with either adjacent matched retained vertex preserves optimality. Therefore all exactly-two-supported outside vertices adjacent to a fixed matched retained vertex are pairwise adjacent, even when their second retained neighbors differ.

Lean 4.19.0, Mathlib v4.19.0. Import only the checked `Proof384b` object from `graffiti-384b-partial/src/Proof384b.lean`. Replay with `lean -j1 -DElab.async=false -DwarningAsError=true BiasedCut384b.lean` and your same-pin Mathlib/Proof384b object paths on LEAN_PATH. The six public theorem audits use only propext, Classical.choice, and Quot.sound.
