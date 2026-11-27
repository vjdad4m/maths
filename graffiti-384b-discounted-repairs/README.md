# Discounted corrections for two-domination

For any sample S, let B be the outside vertices having fewer than two neighbors in S. The usual estimate adds all of B. The general theorem here finds a smaller repair by using edges of the induced graph on B.

Let E consist of vertices of B with three or more neighbors in B, together with those having one neighbor in S and at least one neighbor in B. Then the two-domination number is at most |S| + |B| − ceil(|E|/2). On each side of a maximum cut of B, qualifying vertices have enough neighbors across the cut to make up their deficit in S. Skip the qualifying vertices on the side containing more of them and retain the rest of B. This is an arbitrary-order repair lemma, not a solution of the catalogue conjecture. Its application to #384b requires proving there is a sample with a sufficiently small discounted charge.

* [One neighboring pair](PairRepair.lean).
* [General batch of vertices to skip](BatchRepair.lean).
* [Maximum-cut bound](MaxRepair.lean).

Lean 4.19.0 with pinned Mathlib 4.19.0 compiled each source with warnings as errors and reported only propext, Classical.choice and Quot.sound for the three public declarations. Build [Proof384b.lean](../graffiti-384b-partial/src/Proof384b.lean) first and keep its object and Mathlib on the Lean search path. With the extension build directory first on LEAN_PATH, compile PairRepair, BatchRepair, MaxRepair in that order. The technique adapts the original proof's local maximum-cut estimate to the graph induced by the repairs.
