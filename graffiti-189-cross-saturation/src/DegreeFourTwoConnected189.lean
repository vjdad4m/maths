import CutExtraction189
import ActualDistThree189
import TwoCutFinal189
import AdjacentPins189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem cutpair_connected {a b : V}
    (P : Graffiti189LongestPath.TwoCut.CutPair G a b) (i : Bool) :
    (G.induce (↑(P.H i) : Set V)).Connected := by
  obtain ⟨x,xh,_⟩ := P.hita i
  exact induced_connected_of_joined (P.H i) ⟨x,xh⟩ (P.joined i)

private def split_of_cutpair {a b : V}
    (P : Graffiti189LongestPath.TwoCut.CutPair G a b) : Split G a b where
  L := P.H false
  R := P.H true
  dis := P.dis
  leftOff := P.off false
  rightOff := P.off true
  leftConnected := cutpair_connected P false
  cross := by
    intro x xl y yr xy
    rcases P.closed false x xl y xy with h|h|yl
    · exact (P.off true).1 (h ▸ yr)
    · exact (P.off true).2 (h ▸ yr)
    · exact disjoint_left.mp P.dis yl yr
  leftA := P.hita false
  leftB := P.hitb false
  cover := by
    intro z
    rcases P.all z with h|h|⟨i,zi⟩
    · exact .inl h
    · exact .inr (.inl h)
    cases i
    · exact .inr (.inr (.inl zi))
    · exact .inr (.inr (.inr zi))

theorem traceable_at_actual_two_cut (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤5)
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (a b : V) (ab : a≠b)
    (dis : ¬(G.induce {x : V | x≠a ∧ x≠b}).Connected) :
    ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  by_cases short : Fintype.card V≤17
  · exact Graffiti189LongestPath.TwoCut.traceable_of_order_le_seventeen hc even conn degree short
  have big : 3≤Fintype.card V := by omega
  have del := singleton_deletion_connected conn
  have hi := Graffiti189LongestPath.FourCut.Three.component_card_le_two hc a b ab
    (fun x=>distanceTwo_le_of_even 4 x (even x)) even degree del
  have lo := component_card_gt_one_of_disconnected a b big dis
  have exactly : 2=Nat.card (G.induce {x : V | x≠a ∧ x≠b}).ConnectedComponent := by omega
  by_cases dist : 3≤G.dist a b
  · exact Graffiti189LongestPath.TwoCut.traceable_at_actual_dist_three_cut hc a b ab even degree conn exactly dist
  obtain ⟨P⟩ := Graffiti189LongestPath.TwoCut.exists_cut_pair hc a b ab even degree del exactly
  exact (split_of_cutpair P).traceable_of_cut_distance_at_most_two hc even ab (by omega) conn degree
    (cutpair_connected P true)

/-- Graffiti.pc #189 holds for all two-connected finite simple graphs
at degree threshold four. -/
theorem traceable_degree_four_two_connected (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤5)
    (conn : ∀ C : Finset V,C.card<2 → (G.induce ((↑C : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v) :
    ∃ u v : V,∃ q : G.Walk u v,q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  by_cases conn3 : ∀ C : Finset V,C.card<3 → (G.induce ((↑C : Set V)ᶜ)).Connected
  · exact Graffiti189LongestPath.AdjacentPins.traceable_near_connectivity hc 3 (by decide)
      even conn3 degree
  push_neg at conn3
  obtain ⟨C,C3,cd⟩ := conn3
  have C2 : C.card=2 := by
    by_contra bad
    exact cd (conn C (by omega))
  obtain ⟨a,b,ab,hC⟩ := card_eq_two.mp C2
  apply traceable_at_actual_two_cut hc even conn degree a b ab
  have se : ((↑C : Set V)ᶜ) = {x : V | x≠a ∧ x≠b} := by
    rw [hC]
    ext x
    simp
  rwa [se] at cd

#print axioms traceable_at_actual_two_cut
#print axioms traceable_degree_four_two_connected
end Graffiti189LongestPath.CrossSaturation
