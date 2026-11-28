import SixSingletonMultiZeroBoard189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open Finset
variable {V : Type*} [Fintype V]

abbrev widenPort (j : Fin 9) : Fin 16 := ⟨j.val, by omega⟩

private theorem dark_iff_higher : ∀ i : Fin 16,i∈PortCertificates.D ↔ (9 ≤ i.val) := by decide

/-- Label the marked terminals and all six ports by an ordered tuple; all other
indices label the seven vertices of the dark block. Only coverage is needed. -/
theorem label_nine_and_seven (n : Fintype.card V=16) (q : Fin 9→V) (E : Finset V)
    (d : E.card=7) (cover : ∀ z, (∃ j,q j=z) ∨ z∈E) :
    ∃ e : Fin 16≃V,(∀ j,e (widenPort j)=q j) ∧
      (∀ i,i∈PortCertificates.D ↔ e i∈E) := by
  classical
  let B := ↑(↑PortCertificates.D : Set (Fin 16))
  let B' := ↑(↑E : Set V)
  have ds : Fintype.card B=Fintype.card B' :=
    (Fintype.card_coe PortCertificates.D).trans (((by decide : PortCertificates.D.card=7).trans d.symm).trans
      (Fintype.card_coe E).symm)
  let eb : B≃B' := Fintype.equivOfCardEq ds
  let f (i : Fin 16) : V := if h : i.val<9 then q ⟨i.val,h⟩ else
    (eb ⟨i,(dark_iff_higher i).mpr (Nat.le_of_not_gt h)⟩).val
  have uf (i : Fin 9) : f (widenPort i)=q i := by
    dsimp only [f,widenPort]
    rw [dif_pos i.isLt]
  have df (i : Fin 16) (hi : i∈PortCertificates.D) : f i=(eb ⟨i,hi⟩).val :=
    dif_neg (Nat.not_lt_of_ge ((dark_iff_higher i).mp hi))
  have image (z : V) (hz : z∈E) : ∃ i∈PortCertificates.D,f i=z := by
    let i := eb.symm (⟨z,hz⟩ : B')
    refine ⟨i.val,i.property,?_⟩
    rw [df _ i.property]
    exact congrArg Subtype.val (eb.apply_symm_apply (⟨z,hz⟩ : B'))
  have sur : Function.Surjective f := by
    intro z
    rcases cover z with ⟨j,rfl⟩|hz
    · exact ⟨widenPort j,uf j⟩
    obtain ⟨i,_,e⟩ := image z hz
    exact ⟨i,e⟩
  let e : Fin 16≃V := Equiv.ofBijective f
    ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨sur,by rw [n]; simp⟩)
  refine ⟨e,uf,fun i=>⟨fun hi=>?_,fun hi=>?_⟩⟩
  · change f i∈E
    rw [df i hi]
    exact (eb ⟨i,hi⟩).property
  · obtain ⟨j,jd,ej⟩ := image (e i) hi
    have eq : e j=e i := ej
    rw [←e.injective eq]
    exact jd

#print axioms label_nine_and_seven
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
