import NestedCoreOneControlFinal133
import NestedCoreThreeControlRadius133
import NestedCorePrivateMinimumTwoCoreNoCap133
import C7MultiRadiusFourMean133

namespace Graffiti133NestedThreeControls
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133CoreSeven
  Graffiti133MultiWeighted Graffiti133NestedLongGates Graffiti133NestedOneControl Graffiti133Camby
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

theorem radius_four_minimum_p7_free_core_with_dominating_C7_mean_four
    (H : Hole G 7) (hc : G.Connected) (h4 : FourCycleFree G)
    (h9 : ¬∃ p : Fin 9→V,InducedPath G p) (hr : 4≤radius G)
    (D : Finset V) (dm : MinimalSize G D) (cy : ∀ i,H.c i∈D)
    (d7 : ¬∃ f : Fin 7→(D : Set V),InducedPath (G.induce (D : Set V)) f)
    (dom : ∀ x∈D,Outside H.c x → ∃ i,G.Adj x (H.c i)) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  classical
  let C := (Finset.univ : Finset (Fin 7)).image H.c
  let E := D \ C
  have mc (x : V) : x∈C ↔ ∃ i,H.c i=x := by
    simp [C]
  have ofC (x : V) (xm : x∈C) : x∈D := by
    obtain ⟨i,rfl⟩ := (mc x).mp xm
    exact cy i
  have ext (x : V) (xe : x∈E) : x∈D ∧ Outside H.c x ∧ (contactSet H x).Nonempty := by
    obtain ⟨xd,xc⟩ := Finset.mem_sdiff.mp xe
    have xo : Outside H.c x := fun i e=>xc ((mc x).mpr ⟨i,e.symm⟩)
    obtain ⟨i,hi⟩ := dom x xd xo
    exact ⟨xd,xo,⟨i,(mem_contactSet H x i).mpr hi⟩⟩
  have classify (x : V) (xd : x∈D) : (∃ i,H.c i=x) ∨ x∈E := by
    by_cases h : x∈C
    · exact Or.inl ((mc x).mp h)
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨xd,h⟩)
  let J := G.induce (D : Set V)
  let B := restrictedHole H D cy
  have bd (x : (D : Set V)) (xo : Outside B.c x) : ∃ i,J.Adj x (B.c i) :=
    dom x.val x.property (fun i e=>xo i (Subtype.ext e))
  have bound := (outside_independent_and_core_order B (restricted_c4 h4 D) d7 bd).2
  have eqD : Fintype.card (D : Set V)=D.card := Fintype.card_coe D
  rw [eqD] at bound
  have szC : C.card=7 := by
    simp [C,Finset.card_image_of_injective,H.inj]
  have sum : E.card+C.card=D.card := Finset.card_sdiff_add_card_eq_card ofC
  have sz : E.card≤3 := by omega
  have cases : E.card=0 ∨ E.card=1 ∨ E.card=2 ∨ E.card=3 := by omega
  rcases cases with n|n|n|n
  · have empty : E=∅ := Finset.card_eq_zero.mp n
    have atC (x : V) (xd : x∈D) : ∃ i,H.c i=x := by
      rcases classify x xd with h|e
      · exact h
      · rw [empty] at e
        exact (Finset.not_mem_empty x e).elim
    apply radius_four_dominating_C7_mean_four H hc h4 h9 _ hr
    intro x xo
    rcases dm.1.2 x with xd|⟨y,yd,xy⟩
    · obtain ⟨i,e⟩ := atC x xd
      exact (xo i e.symm).elim
    · obtain ⟨i,e⟩ := atC y yd
      exact ⟨i,e.symm ▸ xy⟩
  · obtain ⟨u,eq⟩ := Finset.card_eq_one.mp n
    obtain ⟨ud,uo,_⟩ := ext u (by simp [eq])
    apply radius_four_minimum_one_control_mean_four H hc h4 h9 hr D dm cy d7 u ud uo
    intro x xd
    rcases classify x xd with h|e
    · exact Or.inl h
    · exact Or.inr (by simpa [eq] using e)
  · obtain ⟨u,v,uv,eq⟩ := Finset.card_eq_two.mp n
    obtain ⟨ud,uo,uh⟩ := ext u (by simp [eq])
    obtain ⟨vd,vo,vh⟩ := ext v (by simp [eq])
    apply radius_four_minimum_two_control_core_mean_four H hc h4 h9 hr D dm cy d7 u v uv ud vd _ uo vo uh vh
    intro x xd
    rcases classify x xd with h|e
    · exact Or.inl h
    · exact Or.inr (by simpa [eq] using e)
  · obtain ⟨u,v,w,uv,uw,vw,eq⟩ := Finset.card_eq_three.mp n
    obtain ⟨ud,uo,uh⟩ := ext u (by simp [eq])
    obtain ⟨vd,vo,vh⟩ := ext v (by simp [eq])
    obtain ⟨wd,wo,wh⟩ := ext w (by simp [eq])
    have small := radius_three_of_three_control_core H hc h4 D cy dm.1.2 d7
      u v w ud vd wd uo vo wo uv uw vw uh vh wh (by
        intro x xd
        rcases classify x xd with h|e
        · exact Or.inl h
        · exact Or.inr (by simpa [eq] using e))
    omega

#print axioms radius_four_minimum_p7_free_core_with_dominating_C7_mean_four
end Graffiti133NestedThreeControls
