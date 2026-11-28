import DegreeFiveSaturatedGateway189
import DegreeFiveTwoThreeBase189

namespace Graffiti189LongestPath.CrossSaturation.Split.Five
open SimpleGraph SimpleGraph.Walk Finset
open private d2 from CrossSaturation189
open private boundary_has_at_least_two from DegreeFiveTwoThreeBase189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} (S : Graffiti189LongestPath.CrossSaturation.Split G a b)
set_option linter.unusedSectionVars false

theorem visible_gateway_subset_second (hc : G.Connected) :
    gatewayVisible S⊆secondA G S.L a := by
  classical
  intro v vv
  obtain ⟨vl,av,_,p,pp,pv⟩ := mem_filter.mp vv
  have ne : a≠v := fun h=>S.leftOff.1 (h.symm ▸ vl)
  exact mem_inter.mpr ⟨vl,d2 hc ne av (mem_filter.mp pp).2 pv⟩

theorem dark_gateway_bounds (hc : G.Connected)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (even : ∀ x,(EvenFrom G x).card≤6) {z r : V}
    (zl : z∈S.L) (bz : G.Adj b z) (ry : r∈gatewayVisible S) (rz : G.Adj r z)
    (link : ∀ t∈gatewayDark S z,G.Adj z t)
    (bound : ∀ t∈gatewayDark S z,∀ u,G.Adj t u → u=z ∨ u=b ∨ u∈gatewayDark S z)
    (cap : (S.L.filter (G.Adj b)).card≤4) :
    (gatewayDark S z).card≤5 ∧ ((gatewayDark S z).filter (G.Adj b)).card≤3 ∧
      ((gatewayDark S z).Nonempty → ∃ t∈gatewayDark S z,G.Adj b t) := by
  classical
  let T := gatewayDark S z
  let B := T.filter (G.Adj b)
  have zOff : z∉T := fun m=>(mem_sdiff.mp m).2 (mem_insert_self _ _)
  have rt : r∉T := fun h=>(mem_sdiff.mp h).2 (mem_insert_of_mem (mem_union_right _ ry))
  obtain ⟨rl,_,rb,_,_,_⟩ := mem_filter.mp ry
  have rne : r≠b := fun h=>S.leftOff.2 (h ▸ rl)
  have sub : T⊆DistanceTwo G r := by
    intro t tt
    have ne : r≠t := fun e=>rt (e.symm ▸ tt)
    have no : ¬G.Adj r t := by
      intro a'
      rcases bound t tt r a'.symm with h|h|h
      · exact rz.ne h
      · exact rne h
      exact rt h
    exact d2 hc ne no rz (link t tt)
  have five := (card_le_card sub).trans (distanceTwo_le_of_even 5 r (even r))
  have zB : z∉B := fun h=>zOff (mem_filter.mp h).1
  have sB : insert z B⊆S.L.filter (G.Adj b) := by
    intro t tt
    rcases mem_insert.mp tt with h|h
    · exact h.symm ▸ mem_filter.mpr ⟨zl,bz⟩
    obtain ⟨tT,bt⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨(mem_sdiff.mp tT).1,bt⟩
  have bc := (card_le_card sB).trans cap
  rw [card_insert_of_not_mem zB] at bc
  refine ⟨five,?_,?_⟩
  · change B.card≤3
    omega
  rintro ⟨t,tt⟩
  apply Classical.byContradiction
  intro no
  have cut : 2≤({z} : Finset V).card := by
    apply boundary_has_at_least_two conn (Q:=T) (W:={z}) (y:=a)
    · exact ⟨t,tt,fun h=>zOff (mem_singleton.mp h ▸ tt)⟩
    · exact fun h=>S.leftOff.1 (mem_sdiff.mp h).1
    · exact fun h=>S.leftOff.1 (mem_singleton.mp h ▸ zl)
    intro v vt u ut vu
    rcases bound v vt u vu with e|e|e
    · exact .inr (mem_singleton.mpr e)
    · exact (no ⟨v,vt,e ▸ vu.symm⟩).elim
    exact (ut e).elim
  rw [card_singleton] at cut
  omega

#print axioms visible_gateway_subset_second
#print axioms dark_gateway_bounds
end Graffiti189LongestPath.CrossSaturation.Split.Five
