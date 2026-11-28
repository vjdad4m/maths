# Graffiti.pc #189: the last six-visible case at an adjacent singleton cut

Scope: the actual finite simple graph is connected, deleting any singleton
keeps it connected, all but at most one vertex have degree at least six, and
each vertex sees at most seven vertices at even shortest-path distance,
counting itself. Removing adjacent cut vertices leaves a singleton plus a
thirteen-vertex shore. This package addresses the six-visible case (six shore
vertices neighboring at least one cut vertex). There is no extra balanced-count
or exclusive-port hypothesis in the public endpoint.

The final theorem is
`Graffiti189LongestPath.CrossSaturation.ThresholdSix.traceable_of_adjacent_singleton_thirteen_six_visible`.
It does not prove the whole degree-six threshold or the full conjecture.

The no-balance and one-balance cases are prior results. A remaining
counterexample must have two balanced dark vertices, left/right exclusive
counts 1/2, and strict dark counts 2/3, up to terminal swapping. We relabel
the original graph by the labels
`[x,y,y',c,c',c'',a,b,s,l,l',r,r',r'',w,w']`.
A fixed finite certificate rules out nontraceability in that exact shape.
Its valuation is the actual adjacency and the predicate of distance exactly
two; a distance-two indicator follows from a two-step walk whose endpoints
are distinct and nonadjacent. Every other semantic clause is justified by
neighbor degrees, bridge witnesses, the even-distance cap, or one of 50
explicit spanning-path lists. The certificate was trimmed to 2,197 root
clauses and 4,707 RUP steps. The Lean theorem checks the proposed RUP proof
term and discharges the root clauses from these mathematical facts.

## Replay

Lean 4.19.0; Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
Build the pinned predecessor objects (including the six-visible one-balance
package), set `LEAN_PATH` to include them, and run:

```sh
./replay.sh | tee replay.log
```

The proof inputs are in `q2-probe/`. They are parsed and checked in Lean, not
accepted on the basis of the external solver's status. The Python generation
scripts are explanatory/reproduction aids and are not part of the trusted
proof. Use the already-trimmed CNF and LRAT when replaying the Lean package.
