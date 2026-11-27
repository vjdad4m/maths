# Adjacent-pair deletion in the cyclic-4 Kelmans class

**This is a conditional reduction, not a solution of Kelmans's conjecture.**

Suppose every finite simple cyclically 4-edge-connected, 3-vertex-connected cubic graph of order divisible by six has a spanning packing of three-vertex paths. Then in **every** graph in the same connectivity class of order congruent to two modulo six, deleting the endpoints of **any** edge leaves a graph with a spanning packing of three-vertex paths. Paths need not be induced.

The formal statement is [`cyclic4_factor_implies_t2`](src/CyclicT2.lean). It uses the cut formulation of cyclic 4-edge-connectivity: no edge boundary of size at most three has at least two vertices on both sides. The equivalence with the usual cyclic-cut formulation for cubic graphs is in the [companion proof](../kelmans-defect-cyclic/src/FourRingCyclicGeometry.lean).

## Affine-plane construction

Delete the endpoints of the prescribed edge. The cell that remains has order divisible by three and four distinct ports, because the cap is triangle-free. Place copies of the cell at the nine points of the affine plane over the field with three elements. Introduce one cubic control vertex for each of the twelve lines. Join the four ports of each cell bijectively to the four controls corresponding to the lines through that point.

The resulting host is simple and cubic, and its order is $9(n-2)+12$, a multiple of six. It lies in the cyclic-4 class. For a cut of size at most three, splitting a cell already costs at least two internal edges, so at most one cell can be split. If unsplit cells have both colors, every differently colored pair of points determines a mixed line, and each mixed line accounts for at most two such pairs. There are at least seven such pairs even after one point is discarded, forcing at least four crossing incidences. If no cell is split and all cells have one color, each opposite-colored control contributes three crossings, so a small cut can separate only a single control. If one cell is split, any control of the opposite color to all unsplit cells costs at least two more crossing edges, so all controls must have the common color. The remaining cut is then the corresponding cut in the original cap with both deleted vertices on the common-color side. This gives a singleton shore, as required.

Now take a full packing of the host. Each control lies in its own path with exactly two cell vertices: controls have no mutual edges and no cell vertex touches two controls. Thus exactly 24 cell vertices are used by paths covering controls. If the deleted-edge cell had no full packing, each of its nine copies would send at least three vertices to the controls. In fact each sends a multiple of three, since its order is divisible by three and the internal paths each cover three vertices; sending zero would give a full cell packing. This would require at least 27 cell vertices, a contradiction.

## Scope and replay

The unrestricted adjacent-pair deletion implication is part of [Kelmans's Theorem 3.1](https://arxiv.org/abs/0910.2766), with the adjacent-pair statement denoted (t2). The construction above is checked within the cyclic-4 class; it does not assume the unrestricted theorem as a premise. This note makes no priority claim.

Use Lean 4.19.0 with the Mathlib 4.19.0 build cache:

    lake env bash /path/to/maths/kelmans-affine-t2/replay.sh

This builds the companion proofs and then the six added modules in a temporary directory with warnings treated as errors.

## Fixed girth variant

The implication also holds within any fixed girth threshold. [AffineGirth.lean](src/AffineGirth.lean) verifies that each cycle of the host gives a cycle in the cap of no greater length. A cycle that stays within one cell already belongs to the cap. For a crossing cycle, close an internal port-to-port segment through one or both restored root vertices; the host uses enough external edges to pay for that closure. Thus the host inherits the girth bound, and the same packing extraction applies. The exact statement is [`cyclic4_factor_at_girth_implies_t2`](src/CyclicT2Girth.lean), with the cycle formulation of the girth threshold checked in [the companion girth bridge](../kelmans-defect-cyclic/src/FourRingGirthGeometry.lean).
