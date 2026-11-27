import FourRingCap

open Finset SimpleGraph
namespace KelmansCactus.FourRingAmplify
open ThreePort Substitute PathSlides ContactSlides NearPerfectCells FourRingBudget FourRingCap
noncomputable section
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
variable {G : SimpleGraph V}

omit [DecidableEq J] in
private theorem defect_count (D : J→Finset V) (sep : (↑(univ : Finset J) : Set J).PairwiseDisjoint D)
    (W : Finset V) :
    ((univ : Finset J).filter (fun i=>¬D i⊆W)).card≤((univ:Finset V)\W).card := by
  classical
  let I := (univ:Finset J).filter (fun i=>¬D i⊆W)
  have extHole (i : ↥I) : ∃ x∈D i.val, x∉W := not_subset.mp (mem_filter.mp i.property).2
  choose f m no using extHole
  have inj : Function.Injective f := by
    intro i j e
    apply Subtype.ext
    by_contra ne
    exact disjoint_left.mp (sep (mem_univ i.val) (mem_univ j.val) ne) (m i) (e.symm ▸ m j)
  have sub : I.attach.image f⊆((univ:Finset V)\W) := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact mem_sdiff.mpr ⟨mem_univ _,no i⟩
  have c := card_le_card sub
  rw [card_image_of_injective _ inj,card_attach] at c
  exact c

/-- A genuine partial packing on a four-port ring of bad double-root
caps must leave at least one hole per three cells. This checks all
seam signatures of the actual packing, not only an abstract automaton. -/
theorem bad_four_caps_force_vacancies {P : Parts V} (ok : PackIn G univ P)
    (D : J→Finset V) (sep : (↑(univ:Finset J):Set J).PairwiseDisjoint D)
    (p q : J→Slot→V) (next : Equiv.Perm J)
    (agree : ∀ i b,p (next i) (false,b)=q i (true,b) ∧ q (next i) (false,b)=p i (true,b))
    (seams : ∀ i,Seam (G:=G) (D i) (p i) (q i))
    (res : ∀ i,(D i).card%3=1)
    (K : J→SimpleGraph V) (r : J→Bool→V)
    (cap : ∀ i,Cap (G:=G) (K i) (D i) (p i) (r i))
    (bad : ∀ i,¬Closed (K i) (insert (r i false) (insert (r i true) (D i)))) :
    Fintype.card J ≤ 3*((univ:Finset V)\P.biUnion id).card := by
  classical
  let W := P.biUnion id
  let poor := (univ:Finset J).filter (fun i=>¬D i⊆W)
  let w : J→Slot→ℕ := fun i s=>width P (D i) (p i s) (q i s)
  have mate (i : J) (b : Bool) : Opposite (w i (true,b)) (w (next i) (false,b)) := by
    have ne : i≠next i := by
      intro eq
      have pin : p (next i) (false,b)∈D (next i) := (seams (next i)).left _
      have qq : q i (true,b)∈D (next i) := (agree i b).1 ▸ pin
      exact (seams i).right _ (eq.symm ▸ qq)
    exact opposite_at_shared_seam ok (seams i) (seams (next i))
      (sep (mem_univ _) (mem_univ _) ne) (true,b) (false,b) (agree i b).1 (agree i b).2
  have qual (i : J) (no : i∉poor) : BadHalves (w i) := by
    have complete : D i⊆W := by
      by_contra! e
      exact no (mem_filter.mpr ⟨mem_univ _,e⟩)
    have part : Signature (G:=G) (D i) (p i) (w i) :=
      signature_of_covered_cell ok complete (seams i)
    refine ⟨fun s=>width_le_two ok ((seams i).right s),?_,?_,?_⟩
    · rw [←profile_sum]
      exact (width_congruence part).trans (res i)
    · intro one
      exact bad i (export_one_caps (cap i) part ((profile_sum _).trans one))
    · rintro ⟨l,rr⟩
      exact bad i (export_balanced_caps (cap i) part l rr)
  have first := ring_budget next w mate poor qual
  have second := defect_count D sep W
  change poor.card≤((univ : Finset V)\W).card at second
  change Fintype.card J≤3*((univ:Finset V)\W).card
  omega

#print axioms bad_four_caps_force_vacancies
end
end KelmansCactus.FourRingAmplify
