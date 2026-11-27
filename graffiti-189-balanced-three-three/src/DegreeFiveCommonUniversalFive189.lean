import DegreeFiveDistanceTwoComponents189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_closed shore_disjoint shore_connected from DegreeFiveActualCut189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Five opposite ports exhaust the distance-two sphere of each common
porter. Connectivity within its own shore then makes that porter universal
there. -/
theorem common_universal_in_shore_at_five
    (hc : G.Connected) (even : ∀ x, (EvenFrom G x).card ≤ 6)
    {C D : (CutGraph (G:=G) a b).ConnectedComponent} (cd : C ≠ D)
    {x : V} (xc : x ∈ Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (five : (cutPorts D).card = 5) :
    ∀ w ∈ Shore C, x ≠ w → G.Adj x w := by
  classical
  have foreign : cutPorts D ⊆ DistanceTwo G x := by
    intro w hw
    obtain ⟨wd,ha|hb⟩ := mem_filter.mp hw
    all_goals
      have wc : w ∉ Shore C := fun h => disjoint_left.mp (shore_disjoint cd) h wd
      have ne : x ≠ w := fun e => wc (Eq.mp (congrArg (fun v : V => v ∈ Shore C) e) xc)
      have no : ¬ G.Adj x w := fun h => by
        rcases shore_closed C x xc w h with rfl|rfl|h
        · exact (shore_off D).1 wd
        · exact (shore_off D).2 wd
        · exact wc h
    · exact d2 hc ne no ax.symm ha
    · exact d2 hc ne no bx.symm hb
  have full : cutPorts D = DistanceTwo G x :=
    eq_of_subset_of_card_le foreign ((distanceTwo_le_of_even 5 x (even x)).trans (by omega))
  have no {w : V} (wc : w∈Shore C) : w ∉ DistanceTwo G x := by
    rw [←full]
    exact fun h => disjoint_left.mp (shore_disjoint cd) wc (mem_filter.mp h).1
  intro w wc xw
  let U := ↑(↑(Shore C) : Set V)
  obtain ⟨p⟩ := (shore_connected C).preconnected (⟨x,xc⟩ : U) ⟨w,wc⟩
  have step {s t : U} (q : (G.induce (↑(Shore C) : Set V)).Walk s t)
      (hs : x=s.val ∨ G.Adj x s.val) : x=t.val ∨ G.Adj x t.val := by
    induction q with
    | nil => exact hs
    | @cons u v t uv q ih =>
      apply ih
      change G.Adj u.val v.val at uv
      rcases hs with he|h
      · exact .inr (he.symm ▸ uv)
      by_cases n : x=v.val
      · exact .inl n
      by_cases a : G.Adj x v.val
      · exact .inr a
      exact (no v.property (d2 hc n a h uv)).elim
  exact (step p (.inl rfl)).resolve_left xw

#print axioms common_universal_in_shore_at_five
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
