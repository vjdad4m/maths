# Exact conditional Kelmans factors at a triangle or singleton junction

This package gives two exact factor constructions with explicit cap and attachment hypotheses. Both assume the cyclically 4-edge-connected factor conjecture, as a Lean theorem hypothesis.

- In [the triangle-junction construction](src/TriangleTerminalDomain.lean), the graph partitions into a triangle, a singleton, and two other sets described by capped graphs. A forbidden root edge controls the first cap's root tile, so that the triangle and singleton can replace it exactly. The cap of order 4 modulo 6 yields a factor on its other vertices by vertex deletion. The theorem states the exact wiring and cap hypotheses.
- In [the two-port construction](src/TriangleTerminalDomain.lean), the singleton is adjacent to a prescribed port of each of two capped sets whose capped orders are 2 modulo 6. Removing the root and that port in each cap leaves two factored sets; the singleton joins the two reserved ports in one more path. A separate set must already admit a factor.

The [seam lemma](src/MinimalSeamExtract.lean) shows that a nontrivial 3-edge cut in a cubic 3-vertex-connected graph has three pairwise vertex-disjoint crossing edges. The [cap-domain lemma](src/MinimalAtomDomain.lean) shows that capping an inclusion-minimal nontrivial shore with one vertex produces a cubic 3-vertex-connected graph whose 3-edge cuts are all trivial.

These are exact statements for restricted configurations. They do not assert that the required junction occurs in every graph with three minimal shores, and they do not resolve Kelmans.

## Replay

From a Lean 4.19.0 project with the Mathlib 4.19.0 build cache:

    lake env bash /path/to/maths/kelmans-triangle-terminal/replay.sh
