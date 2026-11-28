import Boundary

namespace UnionClosedBoundary
open Finset
open scoped BigOperators
variable {V : Type*} [DecidableEq V]

def InterClosed (C : Finset (Finset V)) : Prop :=
  ∀ A ∈ C, ∀ B ∈ C, A ∩ B ∈ C

private theorem card_two_form {S : Finset V} {k : V} (hk : k ∈ S)
    (h : S.card = 2) : ∃ l, k ≠ l ∧ S = {k, l} := by
  have one : (S.erase k).card = 1 := by rw [card_erase_of_mem hk,h]
  obtain ⟨l, hl⟩ := card_eq_one.mp one
  have ne : k ≠ l := by
    intro e; subst l
    exact not_mem_erase k S (hl ▸ mem_singleton_self k)
  exact ⟨l,ne,(insert_erase hk).symm.trans (congrArg (insert k) hl)⟩

private theorem companion {C : Finset (Finset V)} (close : InterClosed C) {k l : V}
    (ne : k ≠ l) (no : {k} ∉ C) (pair : {k,l} ∈ C) {S : Finset V}
    (hS : S ∈ C) (hk : k ∈ S) : l ∈ S := by
  by_contra hl
  have eq : ({k,l} : Finset V) ∩ S = {k} := by
    ext x
    simp only [mem_inter,mem_insert,mem_singleton]
    constructor
    · rintro ⟨rfl | rfl,h⟩
      · rfl
      · exact (hl h).elim
    · rintro rfl
      exact ⟨Or.inl rfl,hk⟩
  exact no (eq ▸ close _ pair S hS)

private theorem count_two {C : Finset (Finset V)} {k l : V}
    (ne : k ≠ l) (T : Finset V) (small : T.card ≤ 3)
    (comp : ∀ S ∈ C, k ∈ S → l ∈ S) : (omits C k T).card ≤ 2 := by
  apply card_le_card_of_injOn (fun S => if S = ({k,l} : Finset V) then false else true)
    (t := (univ : Finset Bool))
  · intro S _; exact mem_univ _
  · intro A ha B hb e
    obtain ⟨hAC,hAT,hAk⟩ := mem_filter.mp ha
    obtain ⟨hBC,hBT,hBk⟩ := mem_filter.mp hb
    have hAl := comp A hAC hAk
    have hBl := comp B hBC hBk
    have full (S : Finset V) (sk : k ∈ S) (sl : l ∈ S) (st : S ⊆ T)
        (hne : S ≠ {k,l}) : S = T := by
      have sub : ({k,l} : Finset V) ⊆ S := by simpa [insert_subset_iff] using And.intro sk sl
      have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,Ne.symm hne⟩)
      have hp : ({k,l} : Finset V).card = 2 := by simp [ne]
      exact eq_of_subset_of_card_le st (by omega)
    by_cases hA : A = {k,l} <;> by_cases hB : B = {k,l} <;> simp [hA,hB] at e
    · exact hA.trans hB.symm
    · exact (full A hAk hAl hAT hA).trans (full B hBk hBl hBT hB).symm

/-- If a singleton is missing, one fixed coordinate works for every
window of size at most three. -/
theorem third_pointwise_of_missing (C : Finset (Finset V)) (empty : ∅ ∈ C)
    (close : InterClosed C) (missing : ∃ k : V, {k} ∉ C) :
    ∃ k : V, ∀ T : Finset V, T.card ≤ 3 →
      (omits C k T).card ≤ (contains C k T).card := by
  classical
  have bot (k : V) (T : Finset V) : (∅ : Finset V) ∈ contains C k T :=
    mem_filter.mpr ⟨empty,empty_subset _,not_mem_empty _⟩
  by_cases hnp : ∃ k : V, {k} ∉ C ∧ ∀ l, k ≠ l → {k,l} ∉ C
  · obtain ⟨k,no,np⟩ := hnp
    refine ⟨k,fun T small => ?_⟩
    apply card_le_card_of_injOn (fun _ => (∅ : Finset V))
    · intro S _; exact bot k T
    · intro A ha B hb _
      have full (S : Finset V) (hs : S ∈ omits C k T) : S = T := by
        obtain ⟨hc,sub,hk⟩ := mem_filter.mp hs
        have zero : S.card ≠ 0 := by
          intro e; exact not_mem_empty k (card_eq_zero.mp e ▸ hk)
        have one : S.card ≠ 1 := by
          intro e; obtain ⟨l,rfl⟩ := card_eq_one.mp e
          exact no (by simpa [mem_singleton.mp hk] using hc)
        have two : S.card ≠ 2 := by
          intro e; obtain ⟨l,ne,rfl⟩ := card_two_form hk e
          exact np l ne hc
        exact eq_of_subset_of_card_le sub (by omega)
      exact (full A ha).trans (full B hb).symm
  have hasPair : ∀ k : V, {k} ∉ C → ∃ l, k ≠ l ∧ {k,l} ∈ C := by
    intro k hk
    by_contra! hn
    exact hnp ⟨k,hk,hn⟩
  have works (k l : V) (ne : k ≠ l) (comp : ∀ S ∈ C, k ∈ S → l ∈ S)
      (extra : ∀ T : Finset V, T.card ≤ 3 → 2 ≤ (omits C k T).card →
        ∃ j ∈ T, j ≠ k ∧ {j} ∈ C) :
      ∀ T : Finset V, T.card ≤ 3 → (omits C k T).card ≤ (contains C k T).card := by
    intro T small
    have pos : 0 < (contains C k T).card := card_pos.mpr ⟨∅,bot k T⟩
    by_cases h : (omits C k T).card ≤ 1
    · omega
    obtain ⟨j,jT,nj,jC⟩ := extra T small (by omega)
    have mem : ({j} : Finset V) ∈ contains C k T :=
      mem_filter.mpr ⟨jC,singleton_subset_iff.mpr jT,by simpa [eq_comm] using nj⟩
    have lower : 2 ≤ (contains C k T).card := by
      simpa using card_le_card (show {({j} : Finset V), ∅} ⊆ contains C k T by
        simp [insert_subset_iff,mem,bot])
    exact (count_two ne T small comp).trans lower
  by_cases hp : ∃ k l : V, k ≠ l ∧ {k} ∉ C ∧ {l} ∈ C ∧ {k,l} ∈ C
  · obtain ⟨k,l,ne,no,sl,pair⟩ := hp
    have comp := @companion V _ C close k l ne no pair
    refine ⟨k,works k l ne (fun S hS hk => comp hS hk) ?_⟩
    intro T _ count
    obtain ⟨S,hS⟩ := card_pos.mp (show 0 < (omits C k T).card by omega)
    obtain ⟨hC,sub,hk⟩ := mem_filter.mp hS
    exact ⟨l,sub (comp hC hk),ne.symm,sl⟩
  obtain ⟨k,no⟩ := missing
  obtain ⟨l,ne,pair⟩ := hasPair k no
  have nsl : {l} ∉ C := fun hl => hp ⟨k,l,ne,no,hl,pair⟩
  have comp := @companion V _ C close k l ne no pair
  have comp' := @companion V _ C close l k ne.symm nsl (by simpa [pair_comm] using pair)
  refine ⟨k,works k l ne (fun S hS hk => comp hS hk) ?_⟩
  intro T small count
  have ex : ∃ S ∈ omits C k T, S ≠ ({k,l} : Finset V) := by
    by_contra! hn
    have hsub : omits C k T ⊆ {({k,l} : Finset V)} := fun S hs =>
      mem_singleton.mpr (hn S hs)
    have hc := card_le_card hsub
    rw [card_singleton] at hc
    omega
  obtain ⟨S,hs,nS⟩ := ex
  obtain ⟨hSC,hST,hSk⟩ := mem_filter.mp hs
  have hSl := comp hSC hSk
  have non : (S \ ({k,l} : Finset V)).Nonempty := by
    apply sdiff_nonempty.mpr
    intro h
    apply nS
    exact Subset.antisymm h (by simpa [insert_subset_iff] using And.intro hSk hSl)
  obtain ⟨j,hj⟩ := non
  obtain ⟨jS,jnot⟩ := mem_sdiff.mp hj
  have jk : j ≠ k := fun e => jnot (by simp [e])
  have jl : j ≠ l := fun e => jnot (by simp [e])
  have covers : S ⊆ {k,l,j} := by
    have incl : ({k,l,j} : Finset V) ⊆ S := by simp [insert_subset_iff,hSk,hSl,jS]
    have hc : ({k,l,j} : Finset V).card = 3 := by
      simp [ne,jk.symm,jl.symm]
    exact (eq_of_subset_of_card_le incl (by have := card_le_card hST; omega)).ge
  refine ⟨j,hST jS,jk,?_⟩
  by_contra hn
  obtain ⟨i,ji,P⟩ := hasPair j hn
  have iS := companion close ji hn P hSC jS
  rcases (by simpa using covers iS : i = k ∨ i = l ∨ i = j) with ik|il|ij
  · subst i
    have e : l = j := (mem_insert.mp (comp P (by simp))).resolve_right
      (fun h => ne.symm (mem_singleton.mp h))
    exact jl e.symm
  · subst i
    have e : k = j := by simpa [ne,ne.symm] using comp' P (by simp)
    exact jk e.symm
  · exact ji ij.symm


theorem column_balance (T : Finset V) (k : V) (hk : k ∈ T) :
    (omits T.powerset k T).card = (contains T.powerset k T).card := by
  apply le_antisymm
  · apply card_le_card_of_injOn (fun S => S.erase k)
    · intro S hs
      obtain ⟨_,sub,sk⟩ := mem_filter.mp hs
      exact mem_filter.mpr ⟨mem_powerset.mpr ((erase_subset _ _).trans sub),
        (erase_subset _ _).trans sub, not_mem_erase _ _⟩
    · intro A ha B hb e
      exact (insert_erase (mem_filter.mp ha).2.2).symm.trans
        ((congrArg (insert k) e).trans (insert_erase (mem_filter.mp hb).2.2))
  · apply card_le_card_of_injOn (insert k)
    · intro S hs
      have sub : insert k S ⊆ T := insert_subset_iff.mpr ⟨hk,(mem_filter.mp hs).2.1⟩
      exact mem_filter.mpr ⟨mem_powerset.mpr sub,sub,mem_insert_self _ _⟩
    · intro A ha B hb e
      simpa only [erase_insert (mem_filter.mp ha).2.2,erase_insert (mem_filter.mp hb).2.2]
        using congrArg (fun S : Finset V => S.erase k) e

theorem mass_formula (C : Finset (Finset V)) (T : Finset V) :
    (∑ k ∈ T, (((contains C k T).card : ℝ) - (omits C k T).card)) =
      ∑ S ∈ T.powerset, if S ∈ C then ((T.card : ℝ) - 2 * S.card) else 0 := by
  classical
  have L (k : V) : contains C k T = T.powerset.filter (fun S => S ∈ C ∧ k ∉ S) := by
    ext S; simp only [contains,mem_filter,mem_powerset]; tauto
  have R (k : V) : omits C k T = T.powerset.filter (fun S => S ∈ C ∧ k ∈ S) := by
    ext S; simp only [omits,mem_filter,mem_powerset]; tauto
  have l (k : V) : ((contains C k T).card : ℝ) =
      ∑ S ∈ T.powerset, if S ∈ C ∧ k ∉ S then 1 else 0 := by
    rw [L,card_filter,Nat.cast_sum]
    simp
  have r (k : V) : ((omits C k T).card : ℝ) =
      ∑ S ∈ T.powerset, if S ∈ C ∧ k ∈ S then 1 else 0 := by
    rw [R,card_filter,Nat.cast_sum]
    simp
  simp only [l,r,Finset.sum_sub_distrib (s := T)]
  rw [Finset.sum_comm (s := T), Finset.sum_comm (s := T), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S hs
  by_cases hC : S ∈ C
  · have sub : S ⊆ T := mem_powerset.mp hs
    simp only [hC,true_and,ite_true]
    have cast_card (p : V → Prop) [DecidablePred p] :
        ((T.filter p).card : ℝ) = ∑ x ∈ T, if p x then 1 else 0 := by
      rw [card_filter,Nat.cast_sum]
      simp
    rw [← cast_card (fun x => x ∉ S), ← cast_card (fun x => x ∈ S)]
    have eq1 : T.filter (fun x => x ∈ S) = S := by
      ext x
      simp only [mem_filter, and_iff_right_iff_imp]
      exact fun h => sub h
    have eq2 : T.filter (fun x => x ∉ S) = T \ S := by ext x; simp
    rw [eq1,eq2,card_sdiff sub,Nat.cast_sub (card_le_card sub)]
    ring
  · simp [hC]

/-- When all singleton patterns exist, the *sum* of the balances is
nonnegative in each window of size at most four. A fixed element need
not work for all windows. -/
theorem fourth_mass_of_singletons (C : Finset (Finset V)) (empty : ∅ ∈ C)
    (T : Finset V) (singles : ∀ k ∈ T, {k} ∈ C) (small : T.card ≤ 4) :
    0 ≤ ∑ k ∈ T, (((contains C k T).card : ℝ) - (omits C k T).card) := by
  classical
  have baseline : (∑ S ∈ T.powerset, ((T.card : ℝ) - 2 * S.card)) = 0 := by
    have h := mass_formula T.powerset T
    simp only [Finset.sum_ite_mem, inter_self] at h
    rw [← h]
    apply Finset.sum_eq_zero
    intro k hk
    rw [column_balance T k hk,sub_self]
  rw [mass_formula]
  nth_rw 1 [← baseline]
  apply Finset.sum_le_sum
  intro S hS
  by_cases h : S ∈ C
  · simp [h]
  · rw [if_neg h]
    have ge : 2 ≤ S.card := by
      have h0 : S.card ≠ 0 := fun e => h (card_eq_zero.mp e ▸ empty)
      have h1 : S.card ≠ 1 := by
        intro e
        obtain ⟨k,rfl⟩ := card_eq_one.mp e
        exact h (singles k ((mem_powerset.mp hS) (mem_singleton_self k)))
      omega
    have e : T.card ≤ 2 * S.card := by omega
    exact sub_nonpos.mpr (show (T.card : ℝ) ≤ 2 * (S.card : ℝ) by exact_mod_cast e)

theorem weighted_third [Fintype V] [Nonempty V] (C : Finset (Finset V))
    (empty : ∅ ∈ C) (close : InterClosed C)
    (W : Finset (Finset V)) (small : ∀ T ∈ W, T.card ≤ 3)
    (w : Finset V → ℝ) (nonneg : ∀ T ∈ W, 0 ≤ w T) :
    ∃ k : V, (∑ T ∈ W, w T * (if k ∈ T then ((omits C k T).card : ℝ) else 0)) ≤
      ∑ T ∈ W, w T * (if k ∈ T then ((contains C k T).card : ℝ) else 0) := by
  classical
  by_cases singles : ∀ k : V, {k} ∈ C
  · by_contra! h
    have neg : (∑ k : V, ((∑ T ∈ W, w T * (if k ∈ T then ((contains C k T).card : ℝ) else 0)) -
        ∑ T ∈ W, w T * (if k ∈ T then ((omits C k T).card : ℝ) else 0))) < 0 := by
      apply Finset.sum_neg
      · intro k _; exact sub_neg.mpr (h k)
      · exact Finset.univ_nonempty
    have pos : 0 ≤ (∑ k : V, ((∑ T ∈ W, w T * (if k ∈ T then ((contains C k T).card : ℝ) else 0)) -
        ∑ T ∈ W, w T * (if k ∈ T then ((omits C k T).card : ℝ) else 0))) := by
      simp only [← Finset.sum_sub_distrib, ← mul_sub]
      rw [Finset.sum_comm]
      apply Finset.sum_nonneg
      intro T ht
      rw [← Finset.mul_sum]
      apply mul_nonneg (nonneg T ht)
      have eq (k : V) : ((if k ∈ T then ((contains C k T).card : ℝ) else 0) -
          if k ∈ T then ((omits C k T).card : ℝ) else 0) =
          if k ∈ T then (((contains C k T).card : ℝ) - (omits C k T).card) else 0 := by
        split <;> simp_all
      simp only [eq, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact fourth_mass_of_singletons C empty T (fun k _ => singles k) (by have := small T ht; omega)
    exact not_lt_of_ge pos neg
  · obtain ⟨k,hk⟩ := third_pointwise_of_missing C empty close (not_forall.mp singles)
    refine ⟨k,Finset.sum_le_sum fun T hT => mul_le_mul_of_nonneg_left ?_ (nonneg T hT)⟩
    split <;> first | exact_mod_cast hk T (small T hT) | exact le_rfl


section Original
variable [Fintype V] [Nonempty V]

omit [Nonempty V] in
theorem weighted_coefficients_of_windows (F : Finset (Finset V))
    (top : (univ : Finset V) ∈ F)
    (closed : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)
    {d : ℕ}
    (win : ∀ (C : Finset (Finset V)), ∅ ∈ C → InterClosed C →
        ∀ (W : Finset (Finset V)), (∀ T ∈ W, T.card ≤ d) →
        ∀ (w : Finset V → ℝ), (∀ T ∈ W, 0 ≤ w T) →
        ∃ k : V, (∑ T ∈ W, w T * (if k ∈ T then ((omits C k T).card : ℝ) else 0)) ≤
          ∑ T ∈ W, w T * (if k ∈ T then ((contains C k T).card : ℝ) else 0))
    (m : ℕ) (near : Fintype.card V ≤ m+d) (x : V → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∃ k : V, (∑ B ∈ (univ : Finset V).powersetCard m,
          (∏ i ∈ B, x i) * ((absent F k B).card : ℝ)) ≤
      ∑ B ∈ (univ : Finset V).powersetCard m,
          (∏ i ∈ B, x i) * ((present F k B).card : ℝ) := by
  classical
  have bot : ∅ ∈ F.image compl := mem_image.mpr ⟨univ,top,compl_univ⟩
  have cl : InterClosed (F.image compl) := by
    rintro _ hA _ hB
    obtain ⟨A,hAF,rfl⟩ := mem_image.mp hA
    obtain ⟨B,hBF,rfl⟩ := mem_image.mp hB
    exact mem_image.mpr ⟨A ∪ B,closed A hAF B hBF,compl_union A B⟩
  let W := (univ : Finset V).powersetCard m
  have small : ∀ T ∈ W.image compl, T.card ≤ d := by
    intro T hT
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hT
    rw [card_compl, (mem_powersetCard.mp hB).2]
    omega
  obtain ⟨k,hk⟩ := win _ bot cl _ small
    (fun T => ∏ i ∈ Tᶜ, x i) (fun T _ => Finset.prod_nonneg fun i _ => hx i)
  rw [Finset.sum_image (fun _ _ _ _ e => compl_injective e),
      Finset.sum_image (fun _ _ _ _ e => compl_injective e)] at hk
  have a (B : Finset V) :
      (if k ∈ Bᶜ then ((omits (F.image compl) k Bᶜ).card : ℝ) else 0) =
        (absent F k B).card := by
    by_cases h : k ∈ B
    · have z : absent F k B = ∅ := eq_empty_iff_forall_not_mem.mpr fun A ha =>
        (mem_filter.mp ha).2.2 ((mem_filter.mp ha).2.1 h)
      simp [h,z]
    · simp [h,count_absent]
  have b (B : Finset V) :
      (if k ∈ Bᶜ then ((contains (F.image compl) k Bᶜ).card : ℝ) else 0) =
        (present F k B).card := by
    by_cases h : k ∈ B
    · have z : present F k B = ∅ := eq_empty_iff_forall_not_mem.mpr fun A ha =>
        (mem_filter.mp ha).2.2.2 h
      simp [h,z]
    · simpa only [mem_compl,if_pos h] using
        congrArg (fun n : ℕ => (n : ℝ)) (count_present F k B h)
  exact ⟨k,by simpa only [compl_compl,a,b] using hk⟩

/-- Phan's weighted inequality whenever the requested degree is within
three of the order of the ground set. -/
theorem weighted_coefficients_third (F : Finset (Finset V))
    (top : (univ : Finset V) ∈ F)
    (closed : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)
    (m : ℕ) (near : Fintype.card V ≤ m+3) (x : V → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∃ k : V, (∑ B ∈ (univ : Finset V).powersetCard m,
          (∏ i ∈ B, x i) * ((absent F k B).card : ℝ)) ≤
      ∑ B ∈ (univ : Finset V).powersetCard m,
          (∏ i ∈ B, x i) * ((present F k B).card : ℝ) :=
  weighted_coefficients_of_windows F top closed weighted_third m near x hx

omit [DecidableEq V] [Fintype V] [Nonempty V] in
private theorem weighted_counts_transpose (F : Finset (Finset V)) (W : Finset (Finset V))
    (P : Finset V → Finset V → Prop) [∀ B A, Decidable (P B A)]
    (w : Finset V → ℝ) :
    (∑ B ∈ W, w B * ((F.filter (P B)).card : ℝ)) =
      ∑ A ∈ F, ∑ B ∈ W.filter (fun B => P B A), w B := by
  classical
  have card_eq (B : Finset V) :
      ((F.filter (P B)).card : ℝ) = ∑ A ∈ F, if P B A then 1 else 0 := by
    rw [card_filter,Nat.cast_sum]
    simp
  simp only [card_eq, Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  split <;> simp_all

omit [Nonempty V] in
theorem phan_of_coefficients (F : Finset (Finset V))
    (m : ℕ) (x : V → ℝ)
    (coeff : ∃ k : V, (∑ B ∈ (univ : Finset V).powersetCard m,
          (∏ i ∈ B, x i) * ((absent F k B).card : ℝ)) ≤
      ∑ B ∈ (univ : Finset V).powersetCard m,
          (∏ i ∈ B, x i) * ((present F k B).card : ℝ)) :
    ∃ k : V,
      (∑ A ∈ F.filter (fun A => k ∉ A), ∑ B ∈ A.powersetCard m, ∏ i ∈ B, x i) ≤
      ∑ A ∈ F.filter (fun A => k ∈ A), ∑ B ∈ (A.erase k).powersetCard m, ∏ i ∈ B, x i := by
  classical
  obtain ⟨k,h⟩ := coeff
  refine ⟨k,?_⟩
  simp only [absent,present,weighted_counts_transpose] at h
  have a (A : Finset V) :
      ((univ : Finset V).powersetCard m).filter (fun B => B ⊆ A ∧ k ∉ A) =
        if k ∉ A then A.powersetCard m else ∅ := by
    split <;> rename_i hA <;> ext B <;> simp [hA, mem_powersetCard, subset_univ, and_comm]
  have b (A : Finset V) :
      ((univ : Finset V).powersetCard m).filter (fun B => B ⊆ A ∧ k ∈ A ∧ k ∉ B) =
        if k ∈ A then (A.erase k).powersetCard m else ∅ := by
    split <;> rename_i hA <;> ext B <;> simp [hA, mem_powersetCard,subset_univ,subset_erase, and_left_comm, and_comm, and_assoc]
  simp only [a,b] at h
  simp only [Finset.sum_filter]
  convert h using 1 <;> apply Finset.sum_congr rfl <;> intro A _ <;> split <;> simp_all

/-- The nested sums in the posted conjecture, in their original order. -/
theorem phan_third (F : Finset (Finset V))
    (top : (univ : Finset V) ∈ F)
    (closed : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)
    (m : ℕ) (near : Fintype.card V ≤ m+3) (x : V → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∃ k : V,
      (∑ A ∈ F.filter (fun A => k ∉ A), ∑ B ∈ A.powersetCard m, ∏ i ∈ B, x i) ≤
      ∑ A ∈ F.filter (fun A => k ∈ A), ∑ B ∈ (A.erase k).powersetCard m, ∏ i ∈ B, x i :=
  phan_of_coefficients F m x (weighted_coefficients_third F top closed m near x hx)

end Original
#print axioms weighted_coefficients_third
#print axioms phan_third
end UnionClosedBoundary
