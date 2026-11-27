import PentagonStructure133
import NoFiveHoles133

namespace Graffiti133BicycleCharge
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

noncomputable def row (G : SimpleGraph V) (v : V) (S : Finset V) : ℕ :=
  ∑ w ∈ S, @ite ℕ (G.Adj v w) (Classical.propDecidable _) 1 0

private lemma row_card (v : V) (S : Finset V) :
    row G v S = (S.filter fun w => G.Adj v w).card := by
  classical
  exact (Finset.card_filter _ _).symm

private lemma local_bound (v : V) : localIndependence G v ≤ row G v Finset.univ := by
  classical
  obtain ⟨A,hA,eA⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) v
  rw [←eA,row_card]
  exact Finset.card_le_card (fun x hx => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,(Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).1 x hx⟩)

private lemma row_symm (A B : Finset V) :
    (∑ x ∈ A, row G x B) = ∑ y ∈ B, row G y A := by
  classical
  unfold row
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [G.adj_comm y x]

private lemma cycle_row (H : Hole G 7) (i : Fin 7) :
    row G (H.c i) (Finset.univ.image H.c) = 2 := by
  classical
  change (∑ w ∈ Finset.univ.image H.c, (if G.Adj (H.c i) w then 1 else 0 : ℕ))=2
  rw [Finset.sum_image (fun _ _ _ _ eq => H.inj eq)]
  have aux : ∀ i : Fin 7, (Finset.univ.filter fun j => Cyclic i j).card = 2 := by decide
  rw [←aux i,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  exact if_congr (H.adj i j) rfl rfl


private theorem singleton_row (H : Hole G 7) (x : V) (i : Fin 7)
    (hit : ∀ j, G.Adj x (H.c j) ↔ j=i) :
    row G x (Finset.univ.image H.c) = 1 := by
  classical
  change (∑ w ∈ Finset.univ.image H.c, (if G.Adj x w then 1 else 0 : ℕ))=_
  rw [Finset.sum_image (fun _ _ _ _ eq => H.inj eq)]
  have h : (∑ j : Fin 7, (if j=i then 1 else 0 : ℕ)) = 1 := by simp
  have same : (∑ j : Fin 7, (if G.Adj x (H.c j) then 1 else 0 : ℕ)) =
      (∑ j : Fin 7, (if j=i then 1 else 0 : ℕ)) := by
    apply Finset.sum_congr rfl
    intro j _
    exact if_congr (hit j) rfl rfl
  exact same.trans h

theorem singleton_contact_charge (H : Hole G 7)
    (site : ∀ x, Outside H.c x → ∃ i, ∀j, G.Adj x (H.c j) ↔ j=i)
    (exterior : let O := ((Finset.univ : Finset V) \ Finset.univ.image H.c);
      (∑ x∈O, row G x O) ≤ 2*O.card) :
    (∑ v : V, localIndependence G v) ≤ 4*Fintype.card V := by
  classical
  let C : Finset V := Finset.univ.image H.c
  let O : Finset V := Finset.univ \ C
  have old : C.card=7 := by rw [Finset.card_image_of_injective _ H.inj]; simp
  have size : O.card+7=Fintype.card V := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
    rw [old,Finset.card_univ] at h
    exact h
  have out (v : V) (hv : v∈O) : Outside H.c v := by
    intro i e
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)
  have cSum : (∑ v∈C, row G v C)=14 := by
    change (∑ v ∈ Finset.univ.image H.c, row G v C)=14
    rw [Finset.sum_image (fun _ _ _ _ e => H.inj e)]
    have cRow (i : Fin 7) : row G (H.c i) C=2 := cycle_row H i
    simp_rw [cRow]
    simp
  have weight : (∑ v∈O, row G v C)=O.card := by
    have eq (v : V) (hv : v∈O) : row G v C=1 := by
      obtain ⟨i,hi⟩ := site v (out v hv)
      exact singleton_row H v i hi
    rw [Finset.sum_congr rfl eq]
    simp
  have split (f : V → ℕ) : (∑ v : V, f v) = (∑ v∈C,f v)+(∑ v∈O,f v) := by
    simpa [O,Nat.add_comm] using (Finset.sum_sdiff (f:=f) (Finset.subset_univ C)).symm
  have rows (v : V) : row G v Finset.univ = row G v C + row G v O :=
    split (fun w => @ite ℕ (G.Adj v w) (Classical.propDecidable _) 1 0)
  change (∑ x∈O, row G x O) ≤ 2*O.card at exterior
  refine (Finset.sum_le_sum (fun v _ => local_bound v)).trans ?_
  rw [split (fun v => row G v Finset.univ)]
  simp_rw [rows,Finset.sum_add_distrib]
  rw [cSum,row_symm (G:=G) C O,weight]
  omega

#print axioms singleton_contact_charge
end Graffiti133BicycleCharge
