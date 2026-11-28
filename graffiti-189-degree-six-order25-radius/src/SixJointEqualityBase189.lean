import SixThreeJointOrder189

namespace Graffiti189LongestPath
open Finset

/-- A bounded finite family attaining the full sum of its cardinal budgets
has full-sized disjoint members. -/
theorem exact_cover_members {I X : Type*} [DecidableEq I] [DecidableEq X]
    (T : Finset I) (F : I→Finset X) (B : Finset X) (k : ℕ)
    (cov : B⊆T.biUnion F) (card : B.card=T.card*k)
    (lim : ∀ a∈T,(F a).card≤k) :
    (∀ a∈T,(F a).card=k) ∧ (∀ a∈T,∀ b∈T,a≠b → Disjoint (F a) (F b)) := by
  classical
  have cut (a : I) (aT : a∈T) (S : Finset X) (cover : B⊆S∪(T.erase a).biUnion F) :
      k≤S.card := by
    have h := (card_le_card cover).trans (card_union_le S ((T.erase a).biUnion F))
    have l := card_biUnion_le_card_mul (T.erase a) F k (fun b bt=>lim b (mem_erase.mp bt).2)
    rw [card] at h
    have e := card_erase_add_one aT
    have m := congrArg (fun n : ℕ=>n*k) e
    change ((T.erase a).card + 1)*k = T.card*k at m
    rw [Nat.add_mul,one_mul] at m
    omega
  constructor
  · intro a aT
    apply le_antisymm (lim a aT)
    refine cut a aT (F a) ?_
    intro x xm
    obtain ⟨b,bT,xb⟩ := mem_biUnion.mp (cov xm)
    by_cases e : b=a
    · exact mem_union_left _ (e ▸ xb)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨b,mem_erase.mpr ⟨e,bT⟩,xb⟩)
  · intro a aT b bT ab
    apply disjoint_left.mpr
    intro x xa xb
    have small := cut a aT ((F a).erase x) (by
      intro y ym
      obtain ⟨c,cT,yc⟩ := mem_biUnion.mp (cov ym)
      by_cases e : c=a
      · subst c
        by_cases f : y=x
        · exact mem_union_right _ (mem_biUnion.mpr ⟨b,mem_erase.mpr ⟨ab.symm,bT⟩,f.symm ▸ xb⟩)
        · exact mem_union_left _ (mem_erase.mpr ⟨f,yc⟩)
      · exact mem_union_right _ (mem_biUnion.mpr ⟨c,mem_erase.mpr ⟨e,cT⟩,yc⟩))
    have p := lim a aT
    have h := card_erase_add_one xa
    omega

#print axioms exact_cover_members
end Graffiti189LongestPath
