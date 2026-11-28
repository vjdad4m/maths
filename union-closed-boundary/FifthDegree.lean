import FourthDegree

namespace UnionClosedBoundary
open Finset
open scoped BigOperators
variable {V : Type*} [DecidableEq V]

def missingAt (C : Finset (Finset V)) (T : Finset V) (r : ℕ) :=
  (T.powersetCard r).filter (fun A => A ∉ C)

private theorem missing_mem {C : Finset (Finset V)} {T A : Finset V} {r : ℕ} :
    A ∈ missingAt C T r ↔ A ⊆ T ∧ A.card = r ∧ A ∉ C := by
  simp [missingAt,mem_powersetCard,and_assoc]

private theorem missing_quad_of_pair {C : Finset (Finset V)} (close : InterClosed C)
    {T A : Finset V} (five : T.card = 5) (hA : A ∈ missingAt C T 2) :
    (missingAt C T 4).Nonempty := by
  obtain ⟨sub,two,nA⟩ := missing_mem.mp hA
  by_contra h
  have quad (x : V) (xt : x ∈ T) : T.erase x ∈ C := by
    by_contra no
    exact h ⟨_,missing_mem.mpr ⟨erase_subset _ _,by simp [card_erase_of_mem xt,five],no⟩⟩
  have three : (T \ A).card = 3 := by simp [card_sdiff sub,five,two]
  obtain ⟨x,y,z,_,_,_,e⟩ := card_eq_three.mp three
  have xt : x ∈ T := (mem_sdiff.mp (e ▸ mem_insert_self x {y,z})).1
  have yt : y ∈ T := (mem_sdiff.mp (e ▸ (by simp : y ∈ ({x,y,z} : Finset V)))).1
  have zt : z ∈ T := (mem_sdiff.mp (e ▸ (by simp : z ∈ ({x,y,z} : Finset V)))).1
  have eq : (T.erase x ∩ T.erase y) ∩ T.erase z = A := by
    ext k
    have v (hK : k ∈ T) : k ∉ A ↔ k = x ∨ k = y ∨ k = z := by
      have hh : k ∈ T \ A ↔ k ∈ ({x,y,z} : Finset V) := by rw [e]
      simpa [hK] using hh
    simp only [mem_inter,mem_erase]
    by_cases hk : k ∈ T
    · simp only [hk,and_true]
      tauto
    · simp [hk,show k ∉ A from fun ha => hk (sub ha)]
  exact nA (eq ▸ close _ (close _ (quad x xt) _ (quad y yt)) _ (quad z zt))

private theorem missing_triple_incidence {C : Finset (Finset V)} (close : InterClosed C)
    {T : Finset V} (five : T.card = 5) :
    2 * (missingAt C T 2).card ≤ 3 * (missingAt C T 3).card := by
  classical
  let P := missingAt C T 2
  let Q := missingAt C T 3
  have lower (A : Finset V) (hA : A ∈ P) :
      2 ≤ (Q.filter (fun B => A ⊆ B)).card := by
    obtain ⟨sub,two,nA⟩ := missing_mem.mp hA
    let E := T \ A
    have ecard : E.card = 3 := by simp [E,card_sdiff sub,five,two]
    let Bad := E.filter (fun x => insert x A ∈ C)
    have hbad : Bad.card ≤ 1 := by
      by_contra! high
      obtain ⟨x,hx⟩ := card_pos.mp (show 0 < Bad.card by omega)
      have ex : (Bad.erase x).Nonempty := by
        apply card_pos.mp
        rw [card_erase_of_mem hx]
        omega
      obtain ⟨y,hy⟩ := ex
      obtain ⟨yx,hyB⟩ := mem_erase.mp hy
      have eq : insert x A ∩ insert y A = A := by
        ext k
        simp only [mem_inter,mem_insert]
        constructor
        · rintro ⟨h1,h2⟩
          rcases h1 with rfl|h1
          · exact h2.resolve_left yx.symm
          · exact h1
        · exact fun h => ⟨Or.inr h,Or.inr h⟩
      exact nA (eq ▸ close _ (mem_filter.mp hx).2 _ (mem_filter.mp hyB).2)
    have bn : (E \ Bad).card ≥ 2 := by
      rw [card_sdiff (filter_subset _ _),ecard]
      change 2 ≤ 3 - Bad.card
      omega
    refine bn.trans (card_le_card_of_injOn (fun x => insert x A) ?_ ?_)
    · intro x hx
      obtain ⟨hxE,hxB⟩ := mem_sdiff.mp hx
      obtain ⟨xt,xA⟩ := mem_sdiff.mp hxE
      refine mem_filter.mpr ⟨missing_mem.mpr ⟨insert_subset_iff.mpr ⟨xt,sub⟩,
        by simp [card_insert_of_not_mem xA,two],fun hc => hxB (mem_filter.mpr ⟨hxE,hc⟩)⟩,subset_insert _ _⟩
    · intro x hx y _ eq
      change insert x A = insert y A at eq
      have hxA := (mem_sdiff.mp (mem_sdiff.mp hx).1).2
      exact (mem_insert.mp (eq ▸ mem_insert_self x A)).resolve_right hxA
  have upper (B : Finset V) (hB : B ∈ Q) :
      (P.filter (fun A => A ⊆ B)).card ≤ 3 := by
    have h3 := (missing_mem.mp hB).2.1
    calc
      _ ≤ (B.powersetCard 2).card := card_le_card (fun A hA =>
        mem_powersetCard.mpr ⟨(mem_filter.mp hA).2,(missing_mem.mp (mem_filter.mp hA).1).2.1⟩)
      _ = 3 := by rw [card_powersetCard,h3]; decide
  have dbl : (∑ A ∈ P, (Q.filter (fun B => A ⊆ B)).card) =
      ∑ B ∈ Q, (P.filter (fun A => A ⊆ B)).card := by
    simp only [card_filter]
    exact sum_comm
  change 2 * P.card ≤ 3 * Q.card
  calc
    _ = ∑ _ ∈ P, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ A ∈ P, (Q.filter (fun B => A ⊆ B)).card := sum_le_sum lower
    _ = ∑ B ∈ Q, (P.filter (fun A => A ⊆ B)).card := dbl
    _ ≤ ∑ _ ∈ Q, 3 := sum_le_sum upper
    _ = _ := by simp [Nat.mul_comm]

/-- Pair–triple incidence pays for the positive coefficients lost by deleting
two-element patterns in a five-element window. -/
theorem fifth_mass_of_singletons (C : Finset (Finset V)) (empty : ∅ ∈ C)
    (close : InterClosed C) (T : Finset V) (singles : ∀ k ∈ T, {k} ∈ C)
    (small : T.card ≤ 5) : 0 ≤ ∑ k ∈ T, balance C k T := by
  classical
  by_cases h4 : T.card ≤ 4
  · exact fourth_mass_of_singletons C empty T singles h4
  have five : T.card = 5 := by omega
  let P := missingAt C T 2
  let Q := missingAt C T 3
  let R := missingAt C T 4
  have d : 2 * P.card ≤ 3 * Q.card := missing_triple_incidence close five
  have p10 : P.card ≤ 10 := by
    calc
      _ ≤ (T.powersetCard 2).card := card_le_card (filter_subset _ _)
      _ = 10 := by rw [card_powersetCard,five]; decide
  have comp : P.card ≤ Q.card + 3 * R.card := by
    by_cases pos : 0 < P.card
    · have r : 0 < R.card := by
        obtain ⟨A,hA⟩ := card_pos.mp pos
        exact card_pos.mpr (missing_quad_of_pair close five hA)
      omega
    · omega
  have baseline : (∑ S ∈ T.powerset, ((T.card : ℝ) - 2 * S.card)) = 0 := by
    have h := mass_formula T.powerset T
    simp only [Finset.sum_ite_mem,inter_self] at h
    rw [← h]
    exact sum_eq_zero (fun k hk => by rw [column_balance T k hk,sub_self])
  have miss : (∑ k ∈ T, balance C k T) =
      ∑ S ∈ T.powerset, if S ∉ C then (2 * (S.card : ℝ) - T.card) else 0 := by
    unfold balance
    rw [mass_formula]
    have e : (∑ S ∈ T.powerset, if S ∈ C then ((T.card : ℝ) - 2 * S.card) else 0) =
      (∑ S ∈ T.powerset, if S ∈ C then ((T.card : ℝ) - 2 * S.card) else 0)
        - ∑ S ∈ T.powerset, ((T.card : ℝ) - 2 * S.card) := by rw [baseline,sub_zero]
    rw [e,← sum_sub_distrib]
    apply sum_congr rfl
    intro S _
    by_cases h : S ∈ C
    · simp [h]
    · simp [h]
  rw [miss]
  have cr : (P.card : ℝ) ≤ (Q.card : ℝ) + 3 * R.card := by exact_mod_cast comp
  have low : 0 ≤ -(P.card : ℝ) + Q.card + 3 * R.card := by rw [neg_add_eq_sub,sub_add_eq_add_sub]; exact sub_nonneg.mpr cr
  apply low.trans
  have count (r : ℕ) : ((missingAt C T r).card : ℝ) =
      ∑ S ∈ T.powerset, if S.card = r ∧ S ∉ C then 1 else 0 := by
    have e : missingAt C T r = T.powerset.filter (fun S => S.card = r ∧ S ∉ C) := by
      ext S; simp [missing_mem,mem_powerset,and_assoc]
    rw [e,card_filter,Nat.cast_sum]
    simp
  change -( (missingAt C T 2).card : ℝ) + (missingAt C T 3).card +
      3 * (missingAt C T 4).card ≤ _
  simp only [count,← sum_neg_distrib,mul_sum,← sum_add_distrib]
  apply sum_le_sum
  intro S hS
  by_cases hC : S ∈ C
  · simp [hC]
  · have sub := mem_powerset.mp hS
    have smallS : S.card ≤ 5 := (card_le_card sub).trans small
    have ge : 2 ≤ S.card := by
      have n0 : S.card ≠ 0 := fun e => hC (card_eq_zero.mp e ▸ empty)
      have n1 : S.card ≠ 1 := by
        intro e; obtain ⟨k,rfl⟩ := card_eq_one.mp e
        exact hC (singles k (sub (mem_singleton_self k)))
      omega
    have cases : S.card = 2 ∨ S.card = 3 ∨ S.card = 4 ∨ S.card = 5 := by omega
    rcases cases with h|h|h|h <;> norm_num [hC,h,five] <;> simp

#print axioms fifth_mass_of_singletons

/-- Fifth degree for the case in which all implication classes are symmetric.
This includes families whose complement family contains every singleton. -/
theorem fifth_of_symmetric_cores [Fintype V] [Nonempty V]
    (C : Finset (Finset V)) (bot : ∅ ∈ C) (cl : InterClosed C)
    (K : V → Finset V) (core : ∀ k, IsCore C k (K k))
    (symm : ∀ k j, j ∈ K k → K j = K k)
    (W : Finset (Finset V)) (small : ∀ T ∈ W, T.card ≤ 5)
    (w : Finset V → ℝ) (nn : ∀ T ∈ W, 0 ≤ w T) :
    ∃ k : V, 0 ≤ ∑ T ∈ W, w T * (if k ∈ T then balance C k T else 0) := by
  obtain ⟨P,hn,hm⟩ := symmetric_mass fifth_mass_of_singletons C bot cl K core symm
  exact averaged P hn W w nn (fun T ht => hm T (small T ht))

#print axioms fifth_of_symmetric_cores

/-- The posted inequality for degrees within five of n, when non-occurrence
in the original family forces only mutual implications. -/
theorem phan_fifth_of_symmetric_complements [Fintype V] [Nonempty V]
    (F : Finset (Finset V)) (top : (univ : Finset V) ∈ F)
    (cl : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)
    (K : V → Finset V) (core : ∀ k, IsCore (F.image compl) k (K k))
    (symm : ∀ k j, j ∈ K k → K j = K k)
    (m : ℕ) (near : Fintype.card V ≤ m+5) (x : V → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∃ k : V,
      (∑ A ∈ F.filter (fun A => k ∉ A), ∑ B ∈ A.powersetCard m, ∏ i ∈ B, x i) ≤
      ∑ A ∈ F.filter (fun A => k ∈ A), ∑ B ∈ (A.erase k).powersetCard m, ∏ i ∈ B, x i := by
  classical
  -- The transport from complements to coefficient counts uses only the image
  -- of F. A hypothesis on that image is enough for the window bound.
  apply phan_of_coefficients F m x
  have bot : ∅ ∈ F.image compl := mem_image.mpr ⟨univ,top,compl_univ⟩
  have closed : InterClosed (F.image compl) := by
    intro S hS T hT
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hS
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hT
    exact mem_image.mpr ⟨A ∪ B,cl A hA B hB,compl_union A B⟩
  let W := (univ : Finset V).powersetCard m
  have small : ∀ T ∈ W.image compl, T.card ≤ 5 := by
    intro T hT
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hT
    rw [card_compl,(mem_powersetCard.mp hB).2]
    omega
  obtain ⟨k,hk⟩ := fifth_of_symmetric_cores (F.image compl) bot closed K core symm
    (W.image compl) small (fun T => ∏ i ∈ Tᶜ, x i)
    (fun T _ => Finset.prod_nonneg fun i _ => hx i)
  rw [Finset.sum_image (fun _ _ _ _ e => compl_injective e)] at hk
  refine ⟨k,sub_nonneg.mp ?_⟩
  rw [← sum_sub_distrib]
  convert hk using 1
  apply sum_congr rfl
  intro B _
  rw [← mul_sub,compl_compl]
  by_cases b : k ∈ B
  · have a0 : absent F k B = ∅ := eq_empty_iff_forall_not_mem.mpr fun A ha =>
      (mem_filter.mp ha).2.2 ((mem_filter.mp ha).2.1 b)
    have p0 : present F k B = ∅ := eq_empty_iff_forall_not_mem.mpr fun A ha =>
      (mem_filter.mp ha).2.2.2 b
    simp [a0,p0,b]
  · simp [b,balance,count_present F k B b,count_absent]

#print axioms phan_fifth_of_symmetric_complements

/-- Any maximum core of size at least four supplies a single coordinate
that works coefficient-by-coefficient in every window of size at most five. -/
theorem fifth_of_large_core (C : Finset (Finset V)) (bot : ∅ ∈ C)
    (K : V → Finset V) (core : ∀ k, IsCore C k (K k))
    (k : V) (maxK : ∀ j, (K j).card ≤ (K k).card)
    (large : 4 ≤ (K k).card) (T : Finset V) (small : T.card ≤ 5) :
    (omits C k T).card ≤ (contains C k T).card :=
  complement_injection bot K core k T maxK (Or.inl (by omega))

#print axioms fifth_of_large_core

/-- A maximum core of size at least three with a strict subcore also
works in all five-element windows, including with arbitrary weights. -/
theorem fifth_of_asymmetric_max_core (C : Finset (Finset V)) (bot : ∅ ∈ C)
    (K : V → Finset V) (core : ∀ k, IsCore C k (K k))
    (k : V) (maxK : ∀ j, (K j).card ≤ (K k).card)
    (large : 3 ≤ (K k).card) (j : V) (jk : j ∈ K k) (strict : K j ≠ K k)
    (T : Finset V) (small : T.card ≤ 5) :
    (omits C k T).card ≤ (contains C k T).card := by
  have sub := (core j).2.2 _ (core k).1 jk
  have no : k ∉ K j := by
    intro yes
    exact strict (Subset.antisymm sub ((core k).2.2 _ (core j).1 yes))
  exact complement_injection bot K core k T maxK
    (Or.inr ⟨by omega,K j,(core j).1,⟨j,(core j).2.1⟩,sub,no⟩)

#print axioms fifth_of_asymmetric_max_core
end UnionClosedBoundary
