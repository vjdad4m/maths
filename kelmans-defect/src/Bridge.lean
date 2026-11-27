import Kelmans
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset
namespace KelmansCactus
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Data of a factor, written separately so the partition can be examined. -/
structure Factor (G : SimpleGraph V) (P : Finset (Finset V)) : Prop where
  tile : ∀ t ∈ P, KelmansStarter.IsTile G t
  disj : ∀ s ∈ P, ∀ t ∈ P, s ≠ t → Disjoint s t
  cover : P.biUnion id = univ

def Mixed (A t : Finset V) := (∃ x ∈ t, x ∈ A) ∧ (∃ y ∈ t, y ∉ A)

/-- All edges exiting A are the same specified edge, oriented inward to outward. -/
def OnlyExit (A : Finset V) (p q : V) : Prop :=
  ∀ x ∈ A, ∀ y ∉ A, G.Adj x y → x = p ∧ y = q

omit [Fintype V] in
theorem ports_mem {A t : Finset V} {p q : V}
    (ex : OnlyExit (G := G) A p q) (tile : KelmansStarter.IsTile G t)
    (mix : Mixed A t) : p ∈ t ∧ q ∈ t := by
  rcases tile.2 with ⟨c,hc,hctr⟩
  rcases mix with ⟨⟨x,hxt,hxa⟩,⟨y,hyt,hya⟩⟩
  by_cases hca : c ∈ A
  · have h := ex c hca y hya (hctr y hyt (by rintro rfl; contradiction))
    simpa [← h.1,← h.2] using And.intro hc hyt
  · have h := ex x hxa c hca (hctr x hxt (by rintro rfl; contradiction)).symm
    simpa [← h.1,← h.2] using And.intro hxt hc

theorem unique_mixed {P : Finset (Finset V)} {A t u : Finset V} {p q : V}
    (ex : OnlyExit (G := G) A p q) (hf : Factor G P)
    (ht : t ∈ P) (hu : u ∈ P) (mt : Mixed A t) (mu : Mixed A u) : t = u := by
  by_contra h
  have h1 := (ports_mem ex (hf.tile t ht) mt).1
  have h2 := (ports_mem ex (hf.tile u hu) mu).1
  exact disjoint_left.mp (hf.disj t ht u hu h) h1 h2

theorem sum_inter {P : Finset (Finset V)} (hf : Factor G P) (A : Finset V) :
    ∑ t ∈ P, (t ∩ A).card = A.card := by
  have hd : (P : Set (Finset V)).PairwiseDisjoint (fun t => t ∩ A) := by
    intro s hs t ht hne
    exact (hf.disj s hs t ht hne).mono inter_subset_left inter_subset_left
  rw [← card_biUnion hd]
  have h : P.biUnion (fun t => t ∩ A) = (P.biUnion id) ∩ A :=
    (Finset.biUnion_inter P id A).symm
  rw [h,hf.cover,univ_inter]

omit [Fintype V] in
theorem pure_dvd {A t : Finset V} (h : ¬ Mixed A t) (ht : t.card = 3) :
    3 ∣ (t ∩ A).card := by
  by_cases hall : t ⊆ A
  · simp [inter_eq_left.mpr hall,ht]
  · obtain ⟨x,hxt,hxa⟩ := Finset.not_subset.mp hall
    have he : t ∩ A = ∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro y hy
      obtain ⟨hyt,hya⟩ := mem_inter.mp hy
      exact h ⟨⟨y,hyt,hya⟩,⟨x,hxt,hxa⟩⟩
    simp [he]

/-- When a factor crosses a bridge, the intersection size of its unique crossing
tile with a side is exactly the side order mod 3. -/
theorem bridge_residue {P : Finset (Finset V)} {A t : Finset V} {p q : V}
    (ex : OnlyExit (G := G) A p q) (hf : Factor G P)
    (ht : t ∈ P) (mt : Mixed A t) : (t ∩ A).card = A.card % 3 := by
  have hD : 3 ∣ ∑ u ∈ P.erase t, (u ∩ A).card := by
    apply Finset.dvd_sum
    intro u hu
    obtain ⟨hne,hum⟩ := mem_erase.mp hu
    exact pure_dvd (fun h => hne (unique_mixed ex hf hum ht h mt)) (hf.tile u hum).1
  have hsum : (∑ u ∈ P.erase t, (u ∩ A).card) + (t ∩ A).card = A.card :=
    (P.sum_erase_add (fun u => (u ∩ A).card) ht).trans (sum_inter hf A)
  obtain ⟨x,hxt,hxa⟩ := mt.2
  have hs : t ∩ A ⊂ t := Finset.ssubset_iff_of_subset inter_subset_left |>.mpr
    ⟨x,hxt,by simp [hxa]⟩
  have hlt := Finset.card_lt_card hs
  have h3 := (hf.tile t ht).1
  omega

/-- Positive residue is equivalent to a crossing tile existing. -/
theorem bridge_crossing_iff {P : Finset (Finset V)} {A : Finset V} {p q : V}
    (ex : OnlyExit (G := G) A p q) (hf : Factor G P) :
    (∃ t ∈ P, Mixed A t) ↔ A.card % 3 ≠ 0 := by
  constructor
  · rintro ⟨t,ht,mt⟩
    rw [← bridge_residue ex hf ht mt]
    obtain ⟨x,hxt,hxa⟩ := mt.1
    exact Nat.ne_of_gt (Finset.card_pos.mpr ⟨x,Finset.mem_inter.mpr ⟨hxt,hxa⟩⟩)
  · contrapose!
    intro h
    have hD : 3 ∣ ∑ t ∈ P, (t ∩ A).card := by
      apply Finset.dvd_sum
      intro t ht
      exact pure_dvd (h t ht) (hf.tile t ht).1
    rw [sum_inter hf A] at hD
    exact Nat.mod_eq_zero_of_dvd hD

#print axioms bridge_residue
#print axioms bridge_crossing_iff
end KelmansCactus
