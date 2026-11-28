import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Lean.Elab.Tactic.Omega

namespace UnionClosedBoundary
open Finset
open scoped BigOperators
variable {V : Type*} [DecidableEq V]

/-- Missing-element patterns in a window. Contains k corresponds to
the original set omitting k. -/
def omits (C : Finset (Finset V)) (k : V) (T : Finset V) :=
  C.filter (fun S => S ⊆ T ∧ k ∈ S)

def contains (C : Finset (Finset V)) (k : V) (T : Finset V) :=
  C.filter (fun S => S ⊆ T ∧ k ∉ S)

omit [DecidableEq V] in
private theorem card_small_iff_empty_or_singleton {S : Finset V} (h : S.card ≤ 1) :
    S = ∅ ∨ ∃ x, S = {x} := by
  rcases S.eq_empty_or_nonempty with e|⟨x,hx⟩
  · exact Or.inl e
  · refine Or.inr ⟨x,?_⟩
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hx)
    simpa using h

/-- One coordinate has nonnegative balance in every window of size up to two,
irrespective of whether the complement family is intersection-closed.
For the original family the only assumption needed is that the full ground set belongs to it. -/
theorem pointwise_boundary [Nonempty V] (C : Finset (Finset V)) (empty : ∅ ∈ C) :
    ∃ k : V, ∀ T : Finset V, T.card ≤ 2 →
      (omits C k T).card ≤ (contains C k T).card := by
  classical
  by_cases hs : ∀ k : V, ({k} : Finset V) ∈ C
  · obtain ⟨k⟩ := ‹Nonempty V›
    refine ⟨k,fun T small => ?_⟩
    apply Finset.card_le_card_of_injOn (fun S : Finset V => S.erase k)
    · intro S hS
      obtain ⟨_,hsub,hk⟩ := mem_filter.mp hS
      have hcard := Finset.card_le_card hsub
      have hb : (S.erase k).card ≤ 1 := by rw [card_erase_of_mem hk]; omega
      have hmem : S.erase k ∈ C := by
        rcases card_small_iff_empty_or_singleton hb with h0|⟨a,ha⟩
        · rw [h0]; exact empty
        · rw [ha]; exact hs a
      exact mem_filter.mpr ⟨hmem,(erase_subset k S).trans hsub,not_mem_erase _ _⟩
    · intro S hS U hU eq
      have sk := (mem_filter.mp hS).2.2
      have uk := (mem_filter.mp hU).2.2
      exact (insert_erase sk).symm.trans ((congrArg (insert k) eq).trans (insert_erase uk))
  · obtain ⟨k,hk⟩ := not_forall.mp hs
    refine ⟨k,fun T small => ?_⟩
    apply Finset.card_le_card_of_injOn (fun _ : Finset V => (∅ : Finset V))
    · intro S _
      exact mem_filter.mpr ⟨empty,empty_subset _,not_mem_empty _⟩
    · intro S hS U hU _
      have full (A : Finset V) (hA : A ∈ omits C k T) : A = T := by
        obtain ⟨hAC,hsub,hkA⟩ := mem_filter.mp hA
        have two : 2 ≤ A.card := by
          by_contra! low
          rcases card_small_iff_empty_or_singleton (by omega : A.card ≤ 1) with e|⟨a,e⟩
          · exact not_mem_empty k (e ▸ hkA)
          · have ka : k = a := mem_singleton.mp (e ▸ hkA)
            subst a
            exact hk (e ▸ hAC)
        exact Finset.eq_of_subset_of_card_le hsub (small.trans two)
      exact (full S hS).trans (full U hU).symm

/-- The inequality holds for arbitrary nonnegative weights on all windows
of size at most two, not merely for weights factoring into vertex weights. -/
theorem weighted_boundary [Nonempty V] (C : Finset (Finset V)) (empty : ∅ ∈ C)
    (W : Finset (Finset V)) (small : ∀ T ∈ W, T.card ≤ 2)
    (w : Finset V → ℝ) (nonneg : ∀ T ∈ W, 0 ≤ w T) :
    ∃ k : V, (∑ T ∈ W, w T * ((omits C k T).card : ℝ)) ≤
      ∑ T ∈ W, w T * ((contains C k T).card : ℝ) := by
  obtain ⟨k,hk⟩ := pointwise_boundary C empty
  refine ⟨k,Finset.sum_le_sum (fun T hT => ?_)⟩
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk T (small T hT)) (nonneg T hT)


section Original
variable [Fintype V]

def present (F : Finset (Finset V)) (k : V) (B : Finset V) :=
  F.filter (fun A => B ⊆ A ∧ k ∈ A ∧ k ∉ B)

def absent (F : Finset (Finset V)) (k : V) (B : Finset V) :=
  F.filter (fun A => B ⊆ A ∧ k ∉ A)

private theorem count_present (F : Finset (Finset V)) (k : V) (B : Finset V)
    (h : k ∉ B) :
    (contains (F.image compl) k Bᶜ).card = (present F k B).card := by
  have e : contains (F.image compl) k Bᶜ = (present F k B).image compl := by
    ext S
    simp only [contains, present,mem_filter,mem_image]
    constructor
    · rintro ⟨⟨A,ha,rfl⟩,sub,hk⟩
      exact ⟨A,⟨ha,compl_subset_compl.mp sub,by simpa using hk,h⟩,rfl⟩
    · rintro ⟨A,⟨ha,sub,hk,_⟩,rfl⟩
      exact ⟨⟨A,ha,rfl⟩,compl_subset_compl.mpr sub,by simpa using hk⟩
  rw [e,Finset.card_image_of_injective _ compl_injective]

private theorem count_absent (F : Finset (Finset V)) (k : V) (B : Finset V) :
    (omits (F.image compl) k Bᶜ).card = (absent F k B).card := by
  have e : omits (F.image compl) k Bᶜ = (absent F k B).image compl := by
    ext S
    simp only [omits, absent,mem_filter,mem_image]
    constructor
    · rintro ⟨⟨A,ha,rfl⟩,sub,hk⟩
      exact ⟨A,⟨ha,compl_subset_compl.mp sub,by simpa using hk⟩,rfl⟩
    · rintro ⟨A,⟨ha,sub,hk⟩,rfl⟩
      exact ⟨⟨A,ha,rfl⟩,compl_subset_compl.mpr sub,by simpa using hk⟩
  rw [e,Finset.card_image_of_injective _ compl_injective]

/-- Written in terms of original sets, all monomials whose support misses
at most two coordinates have simultaneously nonnegative coefficient
for the same k. -/
theorem coefficient_boundary [Nonempty V] (F : Finset (Finset V))
    (top : (univ : Finset V) ∈ F) :
    ∃ k : V, ∀ B : Finset V, Bᶜ.card ≤ 2 → (absent F k B).card ≤ (present F k B).card := by
  have bot : ∅ ∈ F.image compl := mem_image.mpr ⟨univ,top,compl_univ⟩
  obtain ⟨k,hk⟩ := pointwise_boundary _ bot
  refine ⟨k,fun B small => ?_⟩
  by_cases b : k ∈ B
  · have e : absent F k B = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro A ha
      exact (mem_filter.mp ha).2.2 ((mem_filter.mp ha).2.1 b)
    rw [e]; exact Nat.zero_le _
  · rw [← count_absent,← count_present F k B b]
    exact hk Bᶜ small

theorem weighted_coefficients [Nonempty V] (F : Finset (Finset V))
    (top : (univ : Finset V) ∈ F) (m : ℕ) (near : Fintype.card V ≤ m+2)
    (x : V → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∃ k : V, (∑ B ∈ (univ : Finset V).powersetCard m,
          (∏ i ∈ B, x i) * ((absent F k B).card : ℝ)) ≤
      ∑ B ∈ (univ : Finset V).powersetCard m,
          (∏ i ∈ B, x i) * ((present F k B).card : ℝ) := by
  obtain ⟨k,hk⟩ := coefficient_boundary F top
  refine ⟨k,Finset.sum_le_sum (fun B hB => ?_)⟩
  have hBc : Bᶜ.card ≤ 2 := by
    rw [Finset.card_compl, (mem_powersetCard.mp hB).2]
    omega
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk B hBc) (Finset.prod_nonneg fun i _ => hx i)

end Original
#print axioms weighted_coefficients
end UnionClosedBoundary
