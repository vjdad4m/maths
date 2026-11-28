# Sharp shore-cycle thresholds for #189 (partial)

This delta assumes the existing normalized separated-double setting of the
older Hall/fan and shore-routing releases. Write d=k+2, A the universal
omitted shore of order h, x its root, J=A−x, B the exact exterior cut, and
P the longest ambient path. It allows at most one low ambient degree.

* Critical off-path count. A normalized separated-double candidate must
  have a high vertex of induced A-degree floor(h/2); otherwise the prior
  one-exception Ore theorem and the checked fan contradiction apply.
  Consequently `k ≤ floor(h/2)+|B\P|`.
* Marked-cycle equality break. With `k ≤ 2|B\P|+1`, a cycle in J of length
  at least k−1 that misses a vertex w with a neighbor in B certifies a
  contradiction: select w as a fan root and credit its extra cycle-arm
  vertex twice. At h=k+1, if w has no cut neighbor, it is universal in A
  and can instead be inserted into a cycle edge.
* Exact minimum-height ceiling. For h=k+1≥11 and k≥7, every cycle in J
  therefore has length at most k−2; the theorem needs no separate port
  lower bound. For odd h=k+1 this is precisely two missing vertices in
  the extremal cycle of the usual Dirac length.
* Dirac-length dispatcher. For h≥11 and k≥7, a cycle in J of length at
  least `2*(floor(h/2)−1)` suffices to eliminate the separated-double
  case at every height except odd h=k+1. The theorem explicitly assumes
  such a cycle exists. It does not assert the ordinary circumference
  theorem as an axiom; a Lean proof of existence is not supplied here.
* In any finite graph of minimum degree at least two with only one
  possible low-degree vertex, a longest path can be rotated to have
  two high endpoints without changing support. `CyclicSparse189`
  separately proves the two-hole counting lemma for the adjacent
  omitted-vertices subcase of an even extremal cycle.

The marked-route lemma in this delta strengthens the previous exact
version by one unit of slack; the earlier release itself is unchanged.
This is not the unrestricted #189 proof.

**One exceptional row also closed.** `ExceptionalSplit189` builds optimal
defect-cost alternating routes when all cross edges are present except
possibly at one vertex of the larger shore, provided that vertex has at
least three cross neighbors. `StarExceptionalSplit189` eliminates that
split for the actual normalized minimum-height separated-double star
with an independent larger part. The case analysis showing all shortest
Dirac-extremal odd-minimum candidates have this shape remains paper-only.

[Complete pinned Lean sources](proof-sources.tar.gz). Extract the archive and use its replay script.
