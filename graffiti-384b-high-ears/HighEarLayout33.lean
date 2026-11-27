import HighEarOdd33

namespace Graffiti384b.HighEar
open Finset SimpleGraph EarAnchor CliquePivot33
open private CubicShore.half_tight CubicShore.clique_score from CubicDiamondCut33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- In the thin degree-four case the path test forces the only possible
clique to consist of the two exterior neighbors and the entire neighborhood
of the unique cubic. This is an intermediate implication under extremality. -/
theorem four_layout {e a c : V} (de : H.degree e=2) (da : H.degree a=4)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c) (thin : additional H e a c=∅)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (half : Fintype.card V≤2*gamma H) {C : Finset V} (cl : H.IsNClique 5 C) :
    let D := exterior H e a c
    ∃ s t u,H.Adj s t ∧ D={s,t} ∧ s∈C ∧ t∈C ∧ a∉C ∧ c∉C ∧ H.degree u=3 ∧
      H.neighborFinset u=C\D ∧ ∀ y,H.degree y=3 → y=u := by
  classical
  let D := exterior H e a c
  obtain ⟨ds,⟨s,t,st,dsame⟩,options⟩ := four_endpoint H de da ea ec ac pos inj half ⟨C,cl⟩
  change D.card=2 at ds
  change D={s,t} at dsame
  have score : trianglesAt H a=2 := by
    rcases options with val|⟨eq,_⟩
    · exact val.2
    · change additional H e a c=D at eq
      rw [thin] at eq; rw [← eq,card_empty] at ds; omega
  have an : a∉C := fun m => by have := CubicShore.clique_score H cl m; omega
  have dc := (CubicShore.endpoints H de ea ec ac pos inj half ⟨C,cl⟩).2
  have c3 {y : V} (dy : H.degree y=3) : trianglesAt H y=3 := by
    rcases cubic_scores H de dy pos inj with two|three
    · have eq := inj (two.trans score.symm); subst y; omega
    · exact three
  have cover (x : V) (xm : x∈C) (xc : x≠c) (xd : x∉D) : ∃ u,H.degree u=3 ∧ H.Adj u x := by
    apply Classical.byContradiction; intro no
    have safe (v : V) (dv : H.degree v=3) (_ : v∉(∅ : Finset V)) : ¬H.Adj v x := fun edge => no ⟨v,dv,edge⟩
    obtain ⟨y,ym,_,bare⟩ := bare_neighbor H de da.ge dc ea ec ac pos inj (CubicShore.half_tight H half)
      cl (fun h => an h.1) xm (fun eq => an (eq ▸ xm)) xc safe
    have sm : s∈D := dsame ▸ mem_insert_self ..
    have tm : t∈D := dsame ▸ mem_insert_of_mem (mem_singleton_self _)
    change y∈D at ym
    rw [dsame] at ym
    rcases mem_insert.mp ym with h|h
    · subst y; exact xd ((bare t tm st) ▸ tm)
    · have ht := mem_singleton.mp h; subst y; exact xd ((bare s sm st.symm) ▸ sm)
  obtain ⟨x,xm,off⟩ := exists_mem_not_mem_of_card_lt_card
    (show (insert c D).card<C.card by have := card_insert_le c D; rw [cl.2]; omega)
  obtain ⟨xc,xd⟩ := (show x≠c ∧ x∉D by simpa [not_or] using off)
  obtain ⟨u,du,_⟩ := cover x xm xc xd
  have only (v : V) (dv : H.degree v=3) : v=u := inj ((c3 dv).trans (c3 du).symm)
  have inside {z : V} (zm : z∈C) (zc : z≠c) (zd : z∉D) : z∈H.neighborFinset u := by
    obtain ⟨v,dv,edge⟩ := cover z zm zc zd
    exact (H.mem_neighborFinset _ _).mpr (only v dv ▸ edge)
  have cn : c∉C := by
    intro cm
    have inc : C.erase c⊆H.neighborFinset u := by
      intro z zm; obtain ⟨zc,mc⟩ := mem_erase.mp zm
      apply inside mc zc
      intro zd
      have zz := (mem_sdiff.mp zd).1
      have ze : z≠e := fun eq => (mem_sdiff.mp zd).2 (eq ▸ mem_insert_self ..)
      have add := (additional_mem H (e:=e)).mpr ⟨ze,(H.mem_neighborFinset _ _).mp zz,cl.1 cm mc zc.symm⟩
      rw [thin] at add; exact Finset.not_mem_empty _ add
    have count := card_le_card inc
    rw [card_erase_of_mem cm,cl.2,card_neighborFinset_eq_degree,du] at count; omega
  have sub : C\D⊆H.neighborFinset u := fun z m => inside (mem_sdiff.mp m).1 (fun eq => cn (eq ▸ (mem_sdiff.mp m).1)) (mem_sdiff.mp m).2
  have cap := card_le_card sub
  rw [card_neighborFinset_eq_degree,du] at cap
  have count := card_sdiff_add_card_inter C D
  rw [cl.2] at count
  have bound := card_le_card (show C∩D⊆D from inter_subset_right)
  have eqD : C∩D=D := eq_of_subset_of_card_le inter_subset_right (by omega)
  have dC : D⊆C := fun z m => (mem_inter.mp (show z∈C∩D by rw [eqD]; exact m)).1
  have nEq : H.neighborFinset u=C\D := (eq_of_subset_of_card_le sub (by rw [card_neighborFinset_eq_degree,du]; omega)).symm
  exact ⟨s,t,u,st,dsame,dC (dsame ▸ mem_insert_self ..),dC (dsame ▸ mem_insert_of_mem (mem_singleton_self _)),an,cn,du,nEq,only⟩

end Graffiti384b.HighEar
#print axioms Graffiti384b.HighEar.four_layout
