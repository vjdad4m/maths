# Kelmans conjecture: ranked cut and live-ear reductions for Remote T2

**Partial results only.** A (P_3)-factor is a partition into paths on three vertices. Remote T2 asks for a (P_3)-factor in the graph obtained by deleting a prescribed adjacent pair and omitting a suitably remote edge, in the cyclically four-edge-connected cubic setting formalized here. It is an auxiliary target in the Kelmans development.

- [Bridge reduction](src/RemoteAvoid3BridgeAll.lean): all nontrivial bridge cases reduce to isolated-pattern three-edge avoidance on strictly smaller order.
- [Exact minimal-bridge shore size](src/RemoteAvoid3TinyRankBoundary.lean): under the smaller Remote T2 induction hypothesis, if a smallest-order counterexample has a nontrivial bridge, a shore has precisely two or four vertices.
- [Live-ear lift](src/RemoteTinyEarRanked.lean): a suitable smaller cyclic-four tester resolves a genuine size-two shore, even if its factor uses one nominated repair edge. That edge is expanded back through a three-vertex path. The existence of a suitable tester in general is not proved here.

The bridge-free case, the general tester existence problem, Remote T2, and the original Kelmans conjecture are not settled here.

## Replay

From a prepared Lean / Mathlib 4.19.0 checkout, run `lake env bash /path/to/maths/kelmans-remote-t2-ranked-cuts/replay.sh`. The script rebuilds public source dependencies. The archived [strict modular replay](StrictReplay.log) used existing published objects and a minimal import overlay for the three public handle modules; their theorem bodies were unchanged, and all new sources were independently recompiled.
