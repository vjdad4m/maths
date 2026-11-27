import DegreeFiveRouteBasic189

namespace Graffiti189EightTerminal
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option linter.unusedSectionVars false

/-- Label the 2+3+3 split of an eight-vertex graph. -/
theorem exists_terminal_labels (A B : Finset V) (a : A.card=2) (b : B.card=3)
    (sz : Fintype.card V=8) (ab : Disjoint A B) :
    ∃ e : Fin 8 ≃ V, ∀ i : Fin 8,
      (e i∈A ↔ i.val<2) ∧ (e i∈B ↔ 2 ≤ i.val ∧ i.val<5) := by
  classical
  let C := (univ : Finset V) \ (A∪B)
  have c : C.card=3 := by simp [C,card_sdiff,card_union_of_disjoint ab, a,b,sz]
  let fA : Fin 2 ≃ A := (Fintype.equivFinOfCardEq ((Fintype.card_coe A).trans a)).symm
  let fB : Fin 3 ≃ B := (Fintype.equivFinOfCardEq ((Fintype.card_coe B).trans b)).symm
  let fC : Fin 3 ≃ C := (Fintype.equivFinOfCardEq ((Fintype.card_coe C).trans c)).symm
  let f (i : Fin 8) : V :=
    if h : i.val<2 then (fA ⟨i.val,h⟩).val
    else if h' : i.val<5 then (fB ⟨i.val-2,by omega⟩).val
    else (fC ⟨i.val-5,by have := i.isLt; omega⟩).val
  have ap {i : Fin 8} (h : i.val<2) : f i=(fA ⟨i.val,h⟩).val := by simp [f,h]
  have bp {i : Fin 8} (lo : 2 ≤ i.val) (hi : i.val<5) :
      f i=(fB ⟨i.val-2,by omega⟩).val := by simp [f,show ¬i.val<2 by omega,hi]
  have cp {i : Fin 8} (lo : 5 ≤ i.val) : f i=(fC ⟨i.val-5,by have := i.isLt; omega⟩).val := by
    simp [f,show ¬i.val<2 by omega,show ¬i.val<5 by omega]
  have am {i : Fin 8} (h : i.val<2) : f i∈A := by rw [ap h]; exact Subtype.property _
  have bm {i : Fin 8} (lo : 2 ≤ i.val) (hi : i.val<5) : f i∈B := by
    rw [bp lo hi]; exact Subtype.property _
  have cm {i : Fin 8} (lo : 5 ≤ i.val) : f i∉A ∧ f i∉B := by
    have m : f i∈C := by rw [cp lo]; exact Subtype.property _
    simpa [C] using m
  have colors (i : Fin 8) : (f i∈A ↔ i.val<2) ∧ (f i∈B ↔ 2 ≤ i.val ∧ i.val<5) := by
    by_cases ia : i.val<2
    · have aa := am ia
      have bb : f i∉B := fun h=>disjoint_left.mp ab aa h
      simp [aa,bb,ia,show ¬2 ≤ i.val by omega]
    by_cases ib : i.val<5
    · have bb := bm (by omega) ib
      have aa : f i∉A := fun h=>disjoint_left.mp ab h bb
      simp [aa,bb,ia,ib,show 2 ≤ i.val by omega]
    obtain ⟨aa,bb⟩ := cm (show 5 ≤ i.val by omega)
    simp [aa,bb,ia,ib]
  have inj : Function.Injective f := by
    intro i j e
    have aa : i.val<2 ↔ j.val<2 := by rw [←(colors i).1,←(colors j).1,e]
    have bb : (2 ≤ i.val ∧ i.val<5) ↔ (2 ≤ j.val ∧ j.val<5) := by
      rw [←(colors i).2,←(colors j).2,e]
    apply Fin.ext
    by_cases ia : i.val<2
    · rw [ap ia,ap (aa.mp ia)] at e
      exact congrArg (@Fin.val 2) (fA.injective (Subtype.ext e))
    by_cases ib : i.val<5
    · have jb := bb.mp ⟨by omega, ib⟩
      rw [bp (by omega) ib,bp jb.1 jb.2] at e
      have q := congrArg (@Fin.val 3) (fB.injective (Subtype.ext e))
      change i.val-2=j.val-2 at q
      omega
    have jn : ¬ j.val<2 := fun jh => ia (aa.mpr jh)
    have jc : 5 ≤ j.val := by
      by_cases h : j.val<5
      · exact (ib ((bb.mpr ⟨by omega,h⟩).2)).elim
      omega
    rw [cp (by omega),cp jc] at e
    have q := congrArg (@Fin.val 3) (fC.injective (Subtype.ext e))
    change i.val-5=j.val-5 at q
    omega
  have bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨inj,by simp [sz]⟩
  exact ⟨Equiv.ofBijective f bij, colors⟩

#print axioms exists_terminal_labels
end Graffiti189EightTerminal
