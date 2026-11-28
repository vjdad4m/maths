import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SDiff

namespace Graffiti189
open Finset
variable {V : Type*} [DecidableEq V]

/-- If exactly five of two disjoint three-vertex port sets are reached, then
the one missed vertex belongs to just one shore and the other shore is covered. -/
theorem one_missing_of_two_triples
    (C D A : Finset V) (dc : C.card = 3) (dd : D.card = 3)
    (dis : Disjoint C D) (sub : A ⊆ C ∪ D) (cover : 5 ≤ A.card)
    (not_all : A ≠ C ∪ D) :
    ∃ f : V, f ∉ A ∧
      ((f ∈ C ∧ D ⊆ A ∧ C.erase f ⊆ A ∧ (C.erase f).card = 2) ∨
       (f ∈ D ∧ C ⊆ A ∧ D.erase f ⊆ A ∧ (D.erase f).card = 2)) := by
  have cd : (C ∪ D).card=6 := by rw [card_union_of_disjoint dis,dc,dd]
  have five : A.card=5 := by
    have b := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,not_all⟩)
    omega
  have zs : ((C ∪ D) \ A).card=1 := by rw [card_sdiff sub,cd,five]
  obtain ⟨f,hf⟩ := card_eq_one.mp zs
  have hm (v : V) : v ∈ (C ∪ D) \ A ↔ v=f := by rw [hf,mem_singleton]
  have fmem := mem_sdiff.mp ((hm f).mpr rfl)
  refine ⟨f,fmem.2,?_⟩
  have every (v : V) (in_union : v ∈ C ∪ D) (vne : v ≠ f) : v ∈ A := by
    by_cases h : v ∈ A
    · exact h
    · exact (vne ((hm v).mp (mem_sdiff.mpr ⟨in_union,h⟩))).elim
  rcases mem_union.mp fmem.1 with fC|fD
  · left
    refine ⟨fC,?_ ,?_ ,by rw [card_erase_of_mem fC,dc]⟩
    · intro v vd
      exact every v (mem_union_right _ vd) (fun eq =>
        disjoint_left.mp dis fC (eq ▸ vd))
    · intro v hv
      exact every v (mem_union_left _ (mem_erase.mp hv).2) (mem_erase.mp hv).1
  · right
    refine ⟨fD,?_ ,?_ ,by rw [card_erase_of_mem fD,dd]⟩
    · intro v vc
      exact every v (mem_union_left _ vc) (fun eq =>
        disjoint_left.mp dis (eq ▸ vc) fD)
    · intro v hv
      exact every v (mem_union_right _ (mem_erase.mp hv).2) (mem_erase.mp hv).1

#print axioms one_missing_of_two_triples
end Graffiti189
