import SixSingletonFiveShallowRoute189
import SixSingletonLabel189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open FiveAdjacent (label_degree label_even traceable_label)
abbrev I5 := SingletonFive16.V
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem label_five_partition :
    ∀ i : I5, i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i∈SingletonFive16.K ∨ i∈SingletonFive16.D := by decide
private theorem k_five_label_where :
    ∀ i∈SingletonFive16.K,i≠0 ∧ i≠1 ∧ i≠2 ∧ i≠3 ∧ i≠4 := by decide
private theorem d_five_label_where :
    ∀ i∈SingletonFive16.D,i≠0 ∧ i≠1 ∧ i≠2 ∧ i≠3 ∧ i≠4 ∧ i∉SingletonFive16.K := by decide

/-- A cardinality sanity checker and a labeling for the singleton profile's
five marked vertices and the two unmarked blocks. -/
theorem singleton_five_board_label (n : Fintype.card V=16) (a b s x y : V)
    (C D : Finset V) (c4 : C.card=3) (d7 : D.card=8)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z=s ∨ z=x ∨ z=y ∨ z∈C ∨ z∈D) :
    ∃ e : I5≃V,e 0=a ∧ e 1=b ∧ e 2=s ∧ e 3=x ∧ e 4=y ∧
      (∀ i,i∈SingletonFive16.K↔e i∈C) ∧ (∀ i,i∈SingletonFive16.D↔e i∈D) := by
  classical
  let C0 := ↑(↑SingletonFive16.K : Set I5)
  let D0 := ↑(↑SingletonFive16.D : Set I5)
  let C1 := ↑(↑C : Set V)
  let D1 := ↑(↑D : Set V)
  have cs : Fintype.card C0=Fintype.card C1 :=
    (Fintype.card_coe SingletonFive16.K).trans (((by decide : SingletonFive16.K.card=3).trans c4.symm).trans
      (Fintype.card_coe C).symm)
  have ds : Fintype.card D0=Fintype.card D1 :=
    (Fintype.card_coe SingletonFive16.D).trans (((by decide : SingletonFive16.D.card=8).trans d7.symm).trans
      (Fintype.card_coe D).symm)
  let ec : C0≃C1 := Fintype.equivOfCardEq cs
  let ed : D0≃D1 := Fintype.equivOfCardEq ds
  let f (i : I5) : V :=
    if h0 : i=0 then a else
    if h1 : i=1 then b else
    if h2 : i=2 then s else
    if h3 : i=3 then x else
    if h4 : i=4 then y else
    if hc : i∈SingletonFive16.K then (ec ⟨i,hc⟩).val else
    (ed ⟨i,by
      rcases label_five_partition i with h|h|h|h|h|h|h
      · exact (h0 h).elim
      · exact (h1 h).elim
      · exact (h2 h).elim
      · exact (h3 h).elim
      · exact (h4 h).elim
      · exact (hc h).elim
      exact h⟩).val
  have fa : f 0=a := by simp [f]
  have fb : f 1=b := by simp [f]
  have fs : f 2=s := by simp [f]
  have fx : f 3=x := by simp [f]
  have fy : f 4=y := by simp [f]
  have atC (i : I5) (h : i∈SingletonFive16.K) : f i=(ec ⟨i,h⟩).val := by
    obtain ⟨u0,u1,u2,u3,u4⟩ := k_five_label_where i h
    simp [f,u0,u1,u2,u3,u4,h]
  have atD (i : I5) (h : i∈SingletonFive16.D) : f i=(ed ⟨i,h⟩).val := by
    obtain ⟨u0,u1,u2,u3,u4,uC⟩ := d_five_label_where i h
    simp [f,u0,u1,u2,u3,u4,uC]
  have imageC (z : V) (hz : z∈C) : ∃ i∈SingletonFive16.K,f i=z := by
    let i := ec.symm (⟨z,hz⟩ : C1)
    refine ⟨i.val,i.property,?_⟩
    rw [atC _ i.property]
    exact congrArg Subtype.val (ec.apply_symm_apply (⟨z,hz⟩ : C1))
  have imageD (z : V) (hz : z∈D) : ∃ i∈SingletonFive16.D,f i=z := by
    let i := ed.symm (⟨z,hz⟩ : D1)
    refine ⟨i.val,i.property,?_⟩
    rw [atD _ i.property]
    exact congrArg Subtype.val (ed.apply_symm_apply (⟨z,hz⟩ : D1))
  have sur : Function.Surjective f := by
    intro z
    rcases cover z with h|h|h|h|h|h|h
    · exact ⟨0,fa.trans h.symm⟩
    · exact ⟨1,fb.trans h.symm⟩
    · exact ⟨2,fs.trans h.symm⟩
    · exact ⟨3,fx.trans h.symm⟩
    · exact ⟨4,fy.trans h.symm⟩
    · obtain ⟨i,_,e⟩ := imageC z h
      exact ⟨i,e⟩
    obtain ⟨i,_,e⟩ := imageD z h
    exact ⟨i,e⟩
  let e : I5≃V := Equiv.ofBijective f
    ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨sur,by rw [n]; simp⟩)
  refine ⟨e,fa,fb,fs,fx,fy,?_,?_⟩
  · intro i
    constructor
    · intro h
      change f i∈C
      rw [atC i h]
      exact (ec ⟨i,h⟩).property
    intro h
    obtain ⟨j,jc,ej⟩ := imageC (e i) h
    have eq : e j=e i := ej
    rw [←e.injective eq]
    exact jc
  intro i
  constructor
  · intro h
    change f i∈D
    rw [atD i h]
    exact (ed ⟨i,h⟩).property
  intro h
  obtain ⟨j,jd,ej⟩ := imageD (e i) h
  have eq : e j=e i := ej
  rw [←e.injective eq]
  exact jd

#print axioms singleton_five_board_label
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
