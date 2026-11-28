# Separated-double omitted stars and disjoint linkage (#189, partial)

Write `d = k+2`, where deletion of fewer than `k` vertices keeps the graph
connected. Assume every vertex has at most `d+1` vertices at even distance,
including itself. A longest path `P` omits adjacent `x,y`, `x` has degree
at least `d`, and the two attachments of `x` to `P` are separated.
The omitted star `A` is the closed neighborhood of `x` off `P`; set
`h=|A|`.

* `DoubleThirdBudget189`: for `k≥6` (thus `d≥8`), four flank charges
  and the gateway split bound the order by `h+k+kd`.
* `HallLinkage189`: Hall's theorem, applied to a bipartite graph on
  `Fin k ⊕ V`, finds an injective slot matching that links disjoint
  start/end sets (of size at least `k`) when no small vertex deletion
  disconnects the graph. The extraction theorem and adapter are separate.
* `EndpointSplice189`, `FanLower189`, `HookTrim189`: a trimmed
  disjoint vertex linkage from `A` to `P` gives indexed hooks. If
  `A` is Hamilton-connected, successive attachment indices are
  separated by at least `h+1`, and the exterior margins are at least
  `h` each. Thus the graph order is at least `k+(k+2)h`.
* `FanRoutable189`: because `h≥k+1`, the preceding lower bound exceeds
  `h+k+k(k+2)`. The Hamilton-connected branch is impossible once the
  disjoint hooks are given. `RoutableBoundary189` separately proves the
  all-cut-ports-on-path obstruction directly from the exact cut Hall
  matching, independent of the general linkage step.
* `GeneralRootAlternatives189`: if `k≥7` and the boundary has exactly
  `k` vertices, then even allowing one ambient low degree, the star has
  the Hamilton-connected alternative, a replacement two-attachment
  root of degree `d` or `d+1`, or a minimum-degree one-attachment
  replacement root of eccentricity at most three.

None of this proves unrestricted #189. In particular the non-Hamilton-connected
separated double and the one-attachment alternatives are not eliminated here.

`HallOrbit189` extracts simple, pairwise vertex-disjoint routes by following
each Hall matching slot to its first return to a slot. `HallHooks189`
trims its terminal edge into the hook interface. The end-to-end theorem
`MengerRoutable189.routable_double_branch_impossible` closes the
Hamilton-connected separated-double branch **without** assuming the
existence of hooks or that all cut ports lie on the path.

The companion `almost_routable_double_branch_impossible` uses shorter
internal routes of uniformly guaranteed vertex order `H`. If `B` is the
exact cut of size `k`, each member of `B` appears in one of the disjoint
routes, and every member outside the longest path gives positive hook
length. The lower bound becomes
`h + k + (k+1)H + 2|B \ P|`. Consequently this branch is impossible
if `(k+1)H + 2|B \ P| > k(k+2)`; no routing premise is discharged by an
axiom. The common lower bound on internal terminal paths remains a stated
mathematical hypothesis.

[Complete pinned Lean sources](proof-sources.tar.gz). Extract the archive and use its replay script.
