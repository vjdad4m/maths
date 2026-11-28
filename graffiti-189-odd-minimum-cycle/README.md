# Exact odd-minimal cycle equality case (#189, partial)

This delta builds on Hall fan, universal-shore routing, and the sharp
terminal threshold deltas. Put (d=k+2), let (A) be the universal
omitted star of a high normalized separated-double root (x), put
(h=|A|), and let (J=G[A\setminus\{x\}]).

* **Generic cycle geometry.** A short directed arc can be replaced by an
  exterior path; alternatively two parallel directed cuts can be joined
  through an exterior vertex on one side and an exterior bridge on the
  other. Both operations are Lean checked and quantitatively preserve
  the required arc lengths.
* **Exact extremal-cycle shape.** In an ordinary finite graph with a
  longest (2m)-cycle omitting precisely two vertices, with (m≥4),
  one omitted vertex high (degree≥m), the other of degree≥3, and all
  except at most one vertex high, the omitted vertices cannot be
  adjacent. The high omitted vertex identifies the alternating class
  (X), of size (m). The other cycle class plus the two omitted
  vertices makes an independent set of size (m+2). Every high vertex
  in that set sees all of (X). The proof of the one-low case constructs
  a longer cycle if the low omitted vertex hits the wrong class once.
* **Concrete degree transfer.** Removing the universal root drops
  induced degree exactly one. The Hall/parity bound gives
  (h≤2\deg_J(v)+5) for every shore vertex, strengthened to
  (h≤2\deg_J(v)+3) when its ambient degree is high.
* **Odd-minimum branch.** For odd (h=k+1≥11), a cycle of length at
  least (2(\lfloor h/2\rfloor-1)) in (J) is impossible. The sharp
  upper forces equality (exactly two omitted vertices); the split
  connects back to the actual normalized star, where its weighted
  nonconstant endpoint-defect argument rules it out. One low ambient
  exception is included throughout.

The ordinary one-low Dirac/Pósa cycle **existence** theorem is not proved
by this delta. The main conjecture remains open here.

**Exact assembly.** `SeparatedDirac189` combines this branch with all
other (h≥11) separated-double heights. Its concrete assembly found all
premises of the missing one-low circumference interface in (J) for
(d≥12). The named proposition `OneLowCircumference` remains an explicit
hypothesis. No extra graph classification or terminal route premise
remains in this separated-double lane.

[Complete pinned Lean sources](proof-sources.tar.gz). Extract the archive and use its replay script.
