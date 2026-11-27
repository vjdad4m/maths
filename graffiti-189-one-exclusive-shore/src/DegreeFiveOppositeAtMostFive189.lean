import DegreeFiveDistanceTwoComponents189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private CutGraph Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- If one shore has a common porter, the opposite shore has at most five
cut ports in total, even without exclusivity. -/
theorem opposite_ports_card_le_five_of_common
    (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ 6)
    {C D : (CutGraph (G:=G) a b).ConnectedComponent} (cd : C ≠ D)
    {x : V} (xc : x ∈ Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    (cutPorts D).card ≤ 5 := by
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
  exact (card_le_card foreign).trans (distanceTwo_le_of_even 5 x (even x))

#print axioms opposite_ports_card_le_five_of_common
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
