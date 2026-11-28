import ThirdDegree

namespace UnionClosedBoundary
open Finset
open scoped BigOperators
variable {V : Type*} [DecidableEq V]

/-- The least pattern containing k, when k occurs. -/
def IsCore (C : Finset (Finset V)) (k : V) (K : Finset V) : Prop :=
  K ∈ C ∧ k ∈ K ∧ ∀ S ∈ C, k ∈ S → K ⊆ S

theorem core_exists {C : Finset (Finset V)} (cl : InterClosed C)
    (k : V) (h : ∃ S ∈ C, k ∈ S) : ∃ K, IsCore C k K := by
  classical
  obtain ⟨S,hS,sm⟩ := (C.filter (fun S => k ∈ S)).exists_min_image
    (fun S => S.card) (by obtain ⟨A,hA,hk⟩ := h; exact ⟨A,mem_filter.mpr ⟨hA,hk⟩⟩)
  obtain ⟨hSC,hkS⟩ := mem_filter.mp hS
  refine ⟨S,hSC,hkS,fun T hT hkT => ?_⟩
  have hI : S ∩ T ∈ C.filter (fun S => k ∈ S) :=
    mem_filter.mpr ⟨cl S hSC T hT,mem_inter.mpr ⟨hkS,hkT⟩⟩
  rw [← eq_of_subset_of_card_le inter_subset_left (sm _ hI)]
  exact inter_subset_right

private theorem complement_injection
    {C : Finset (Finset V)} (bot : ∅ ∈ C) (K : V → Finset V)
    (core : ∀ k, IsCore C k (K k)) (k : V) (T : Finset V)
    (ub : T.card ≤ 4) (maxK : ∀ j, (K j).card ≤ (K k).card)
    (two : 2 ≤ (K k).card)
    (aux : 3 ≤ (K k).card ∨ ∃ l ∈ K k, l ≠ k ∧ {l} ∈ C) :
    (omits C k T).card ≤ (contains C k T).card := by
  classical
  let A := K k
  have htwo : 2 ≤ A.card := two
  let extra := fun S : Finset V => S \ A
  have extS (S : Finset V) (hS : S ∈ omits C k T) : A ⊆ S :=
    (core k).2.2 S (mem_filter.mp hS).1 (mem_filter.mp hS).2.2
  have bound (S : Finset V) (hS : S ∈ omits C k T) :
      (extra S).card + A.card ≤ 4 := by
    rw [card_sdiff_add_card_eq_card (extS S hS)]
    exact (card_le_card (mem_filter.mp hS).2.1).trans ub
  have recover (S : Finset V) (hS : S ∈ omits C k T) : A ∪ extra S = S :=
    union_sdiff_of_subset (extS S hS)
  have good (S : Finset V) (hS : S ∈ omits C k T) (j : V) (hj : j ∈ extra S) :
      K j ⊆ T ∧ k ∉ K j := by
    have h := mem_sdiff.mp hj
    have sub := (core j).2.2 S (mem_filter.mp hS).1 h.1
    refine ⟨sub.trans (mem_filter.mp hS).2.1,?_⟩
    intro hkj
    have inc := (core k).2.2 _ (core j).1 hkj
    have eq := eq_of_subset_of_card_le inc (maxK j)
    exact h.2 (show j ∈ K k by rw [eq]; exact (core j).2.1)
  let el : (Finset V) → V := fun S => if h : (extra S).Nonempty then h.choose else k
  have elmem (S : Finset V) (h : (extra S).Nonempty) : el S ∈ extra S := by
    simp only [el,dif_pos h]
    exact h.choose_spec
  rcases aux with large|⟨l,lA,lk,lC⟩
  · have hlarge : 3 ≤ A.card := large
    apply card_le_card_of_injOn (fun S => if (extra S).Nonempty then K (el S) else ∅)
    · intro S hS
      split
      · rename_i h
        exact mem_filter.mpr ⟨(core _).1,(good S hS _ (elmem S h)).1,(good S hS _ (elmem S h)).2⟩
      · exact mem_filter.mpr ⟨bot,empty_subset _,not_mem_empty _⟩
    · intro S hS U hU he
      have one (P : Finset V) (hP : P ∈ omits C k T) (nP : (extra P).Nonempty) :
          extra P = {el P} := by
        have b := bound P hP
        apply (eq_of_subset_of_card_le (singleton_subset_iff.mpr (elmem P nP)) _).symm
        rw [card_singleton]
        omega
      by_cases h : (extra S).Nonempty <;> by_cases h' : (extra U).Nonempty
      · simp only [if_pos h,if_pos h'] at he
        have elS := (core (el S)).2.1
        have hu : el S ∈ U := (core (el U)).2.2 U (mem_filter.mp hU).1
          (mem_sdiff.mp (elmem U h')).1 (he ▸ elS)
        have eq : el S = el U := by
          have z : el S ∈ extra U := mem_sdiff.mpr ⟨hu,(mem_sdiff.mp (elmem S h)).2⟩
          rwa [one U hU h',mem_singleton] at z
        rw [← recover S hS,← recover U hU,one S hS h,one U hU h',eq]
      · simp only [if_pos h,if_neg h'] at he
        exact (not_mem_empty _ (he ▸ (core (el S)).2.1)).elim
      · simp only [if_neg h,if_pos h'] at he
        exact (not_mem_empty _ (he.symm ▸ (core (el U)).2.1)).elim
      · rw [← recover S hS,← recover U hU,not_nonempty_iff_eq_empty.mp h,not_nonempty_iff_eq_empty.mp h']
  · have aux2 (S : Finset V) (hS : S ∈ omits C k T) : (extra S).card ≤ 2 := by
      have b := bound S hS
      omega
    let f := fun S : Finset V =>
      if (extra S).card = 2 then ({l} : Finset V)
      else if (extra S).Nonempty then K (el S) else ∅
    apply card_le_card_of_injOn f
    · intro S hS
      dsimp only [f]
      split
      · exact mem_filter.mpr ⟨lC,singleton_subset_iff.mpr ((mem_filter.mp hS).2.1 (extS S hS lA)),by simpa using lk.symm⟩
      · split
        · rename_i h
          exact mem_filter.mpr ⟨(core _).1,(good S hS _ (elmem S h)).1,(good S hS _ (elmem S h)).2⟩
        · exact mem_filter.mpr ⟨bot,empty_subset _,not_mem_empty _⟩
    · intro S hS U hU eq
      have tag (P : Finset V) (hP : P ∈ omits C k T) :
          (extra P).card = 2 ↔ f P = {l} := by
        dsimp only [f]
        split
        · simp_all
        · rename_i no
          simp only [no,false_iff]
          split
          · rename_i ne
            intro e
            have hp := (core (el P)).2.1
            rw [e] at hp
            exact (mem_sdiff.mp (elmem P ne)).2 (mem_singleton.mp hp ▸ lA)
          · exact fun e => not_mem_empty l (e.symm ▸ mem_singleton_self l)
      by_cases h : (extra S).card = 2
      · have h' := (tag U hU).mpr (eq ▸ (tag S hS).mp h)
        have full (P : Finset V) (hP : P ∈ omits C k T) (h2 : (extra P).card = 2) : P = T := by
          have hh := card_sdiff_add_card_eq_card (extS P hP)
          change (extra P).card + A.card = P.card at hh
          rw [h2] at hh
          exact eq_of_subset_of_card_le (mem_filter.mp hP).2.1 (by omega)
        exact (full S hS h).trans (full U hU h').symm
      · have h' : (extra U).card ≠ 2 := fun ht => h ((tag S hS).mpr (eq.symm ▸ (tag U hU).mp ht))
        dsimp only [f] at eq
        simp only [if_neg h, if_neg h'] at eq
        have one (P : Finset V) (hP : P ∈ omits C k T)
            (nP : (extra P).Nonempty) (n2 : (extra P).card ≠ 2) :
            extra P = {el P} := by
          have b := aux2 P hP
          exact (eq_of_subset_of_card_le (singleton_subset_iff.mpr (elmem P nP))
            (by rw [card_singleton]; omega)).symm
        by_cases s : (extra S).Nonempty <;> by_cases u : (extra U).Nonempty
        · simp only [if_pos s,if_pos u] at eq
          have hu : el S ∈ U := (core (el U)).2.2 U (mem_filter.mp hU).1
            (mem_sdiff.mp (elmem U u)).1 (eq ▸ (core (el S)).2.1)
          have e : el S = el U := by
            have z : el S ∈ extra U := mem_sdiff.mpr ⟨hu,(mem_sdiff.mp (elmem S s)).2⟩
            rwa [one U hU u h',mem_singleton] at z
          rw [← recover S hS,← recover U hU,one S hS s h,one U hU u h',e]
        · simp only [if_pos s,if_neg u] at eq
          exact (not_mem_empty _ (eq ▸ (core (el S)).2.1)).elim
        · simp only [if_neg s,if_pos u] at eq
          exact (not_mem_empty _ (eq.symm ▸ (core (el U)).2.1)).elim
        · rw [← recover S hS,← recover U hU,not_nonempty_iff_eq_empty.mp s,not_nonempty_iff_eq_empty.mp u]


def balance (C : Finset (Finset V)) (k : V) (T : Finset V) : ℝ :=
  (contains C k T).card - (omits C k T).card

theorem averaged {C : Finset (Finset V)} (P : Finset V) (hn : P.Nonempty)
    (W : Finset (Finset V)) (w : Finset V → ℝ) (nn : ∀ T ∈ W, 0 ≤ w T)
    (mass : ∀ T ∈ W, 0 ≤ ∑ k ∈ P ∩ T, balance C k T) :
    ∃ k : V, 0 ≤ ∑ T ∈ W, w T * (if k ∈ T then balance C k T else 0) := by
  classical
  by_contra! h
  have neg : (∑ k ∈ P, ∑ T ∈ W, w T * (if k ∈ T then balance C k T else 0)) < 0 :=
    sum_neg (fun k _ => h k) hn
  rw [sum_comm] at neg
  refine (not_lt_of_ge (sum_nonneg (fun T ht => ?_))) neg
  rw [← mul_sum]
  apply mul_nonneg (nn T ht)
  rw [← sum_filter, filter_mem_eq_inter]
  exact mass T ht

theorem symmetric_mass [Fintype V] [Nonempty V] {d : ℕ}
    (localMass : ∀ (Q : Finset (Finset V)), ∅ ∈ Q → InterClosed Q →
      ∀ U : Finset V, (∀ k ∈ U, {k} ∈ Q) → U.card ≤ d →
        0 ≤ ∑ k ∈ U, balance Q k U)
    (C : Finset (Finset V)) (bot : ∅ ∈ C) (cl : InterClosed C) (K : V → Finset V)
    (core : ∀ k, IsCore C k (K k))
    (symm : ∀ k j, j ∈ K k → K j = K k) :
    ∃ P : Finset V, P.Nonempty ∧
      ∀ T : Finset V, T.card ≤ d → 0 ≤ ∑ k ∈ P ∩ T, balance C k T := by
  classical
  let pick (S : Finset V) (h : S.Nonempty) := h.choose
  let rep (k : V) := pick (K k) ⟨k,(core k).2.1⟩
  have repK (k : V) : rep k ∈ K k := by
    exact Exists.choose_spec (show (K k).Nonempty from ⟨k,(core k).2.1⟩)
  have same (k j : V) (h : j ∈ K k) : rep j = rep k := by
    unfold rep
    congr 1
    exact symm k j h
  have idem (k : V) : rep (rep k) = rep k := same _ _ (repK k)
  let P := univ.filter (fun k => rep k = k)
  have inP (k : V) : rep k ∈ P := mem_filter.mpr ⟨mem_univ _,idem k⟩
  have pRep (k : V) (hk : k ∈ P) : rep k = k := (mem_filter.mp hk).2
  have co (S : Finset V) (hS : S ∈ C) (k : V) : k ∈ S ↔ rep k ∈ S := by
    constructor
    · intro h; exact (core k).2.2 S hS h (repK k)
    · intro h
      have m := (core (rep k)).2.2 S hS h
      rw [symm k (rep k) (repK k)] at m
      exact m (core k).2.1
  refine ⟨P,⟨rep (Classical.choice ‹Nonempty V›),inP _⟩,?_⟩
  intro T small
  let U := (P ∩ T).filter (fun k => K k ⊆ T)
  let Q := C.image (fun S => S ∩ P)
  have usub : U ⊆ P ∩ T := filter_subset _ _
  have ucard : U.card ≤ d := (card_le_card (usub.trans inter_subset_right)).trans small
  have empty : ∅ ∈ Q := mem_image.mpr ⟨∅,bot,empty_inter _⟩
  have sing (k : V) (hk : k ∈ U) : {k} ∈ Q := by
    have kp : k ∈ P := (mem_inter.mp (usub hk)).1
    refine mem_image.mpr ⟨K k,(core k).1,?_⟩
    ext j
    constructor
    · intro h
      obtain ⟨hjk,jp⟩ := mem_inter.mp h
      exact mem_singleton.mpr ((pRep j jp).symm.trans ((same k j hjk).trans (pRep k kp)))
    · intro h
      rw [mem_singleton.mp h]
      exact mem_inter.mpr ⟨(core k).2.1,kp⟩
  have eq_sub (S : Finset V) (hS : S ∈ C) : S ∩ P ⊆ U ↔ S ⊆ T := by
    constructor
    · intro sub k hk
      have hr := sub (mem_inter.mpr ⟨(co S hS k).mp hk,inP k⟩)
      have inc := (mem_filter.mp hr).2
      rw [symm k (rep k) (repK k)] at inc
      exact inc (core k).2.1
    · intro sub k hk
      obtain ⟨ks,kp⟩ := mem_inter.mp hk
      exact mem_filter.mpr ⟨mem_inter.mpr ⟨kp,sub ks⟩,((core k).2.2 S hS ks).trans sub⟩
  have inj : Set.InjOn (fun S : Finset V => S ∩ P) (↑C : Set (Finset V)) := by
    intro S hS R hR e
    ext k
    rw [co S hS,co R hR]
    have h (A : Finset V) : rep k ∈ A ∩ P ↔ rep k ∈ A := by simp [inP]
    change S ∩ P = R ∩ P at e
    rw [← h S,e,h R]
  have counts (k : V) (hk : k ∈ U) (test : Prop → Prop)
      [∀ p, Decidable (test p)] :
      (Q.filter (fun S => S ⊆ U ∧ test (k ∈ S))).card =
        (C.filter (fun S => S ⊆ T ∧ test (k ∈ S))).card := by
    have kp : k ∈ P := (mem_inter.mp (usub hk)).1
    have eq : Q.filter (fun S => S ⊆ U ∧ test (k ∈ S)) =
        (C.filter (fun S => S ⊆ T ∧ test (k ∈ S))).image (fun S => S ∩ P) := by
      ext S
      simp only [Q,mem_filter,mem_image]
      constructor
      · rintro ⟨⟨A,hA,rfl⟩,sub,hkA⟩
        exact ⟨A,⟨hA,(eq_sub A hA).mp sub,by simpa [kp] using hkA⟩,rfl⟩
      · rintro ⟨A,⟨hA,sub,hkA⟩,rfl⟩
        exact ⟨⟨A,hA,rfl⟩,(eq_sub A hA).mpr sub,by simpa [kp] using hkA⟩
    rw [eq,card_image_of_injOn]
    exact inj.mono fun _ h => (mem_filter.mp h).1
  have Qcl : InterClosed Q := by
    intro A hA B hB
    obtain ⟨X,hX,rfl⟩ := mem_image.mp hA
    obtain ⟨Y,hY,rfl⟩ := mem_image.mp hB
    refine mem_image.mpr ⟨X ∩ Y,cl X hX Y hY,?_⟩
    ext k; simp only [mem_inter]; tauto
  have mass := localMass Q empty Qcl U sing ucard
  have mass' : 0 ≤ ∑ k ∈ U, balance C k T := by
    convert mass using 1
    apply sum_congr rfl
    intro k hk
    change _ = (((Q.filter (fun S => S ⊆ U ∧ ¬ k ∈ S)).card : ℝ) -
      ((Q.filter (fun S => S ⊆ U ∧ k ∈ S)).card : ℝ))
    have c1 : (contains Q k U).card = (contains C k T).card := by
      convert counts k hk Not using 1 <;> congr 1 <;> ext S <;> simp [contains]
    have c2 : (omits Q k U).card = (omits C k T).card := by
      convert counts k hk id using 1 <;> congr 1 <;> ext S <;> simp [omits]
    change balance C k T = ((contains Q k U).card : ℝ) - (omits Q k U).card
    rw [c1,c2]
    rfl
  refine mass'.trans (sum_le_sum_of_subset_of_nonneg usub (fun k hk hku => ?_))
  have no : omits C k T = ∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro S h
    obtain ⟨sc,st,sk⟩ := mem_filter.mp h
    exact hku (mem_filter.mpr ⟨hk,((core k).2.2 S sc sk).trans st⟩)
  simp [balance,no]


theorem weighted_fourth [Fintype V] [Nonempty V] (C : Finset (Finset V))
    (bot : ∅ ∈ C) (cl : InterClosed C)
    (W : Finset (Finset V)) (small : ∀ T ∈ W, T.card ≤ 4)
    (w : Finset V → ℝ) (nn : ∀ T ∈ W, 0 ≤ w T) :
    ∃ k : V, (∑ T ∈ W, w T * (if k ∈ T then ((omits C k T).card : ℝ) else 0)) ≤
      ∑ T ∈ W, w T * (if k ∈ T then ((contains C k T).card : ℝ) else 0) := by
  classical
  have point (k : V) (h : ∀ T ∈ W, (omits C k T).card ≤ (contains C k T).card) :
      (∑ T ∈ W, w T * (if k ∈ T then ((omits C k T).card : ℝ) else 0)) ≤
        ∑ T ∈ W, w T * (if k ∈ T then ((contains C k T).card : ℝ) else 0) := by
    apply sum_le_sum
    intro T ht
    apply mul_le_mul_of_nonneg_left _ (nn T ht)
    split <;> first | exact_mod_cast h T ht | rfl
  by_cases occ : ∀ k : V, ∃ S ∈ C, k ∈ S
  · choose K core using fun k => core_exists cl k (occ k)
    obtain ⟨k,_,maxK⟩ := (univ : Finset V).exists_max_image (fun k => (K k).card) univ_nonempty
    by_cases large : 3 ≤ (K k).card
    · exact ⟨k,point k fun T ht =>
        complement_injection bot K core k T (small T ht) (fun j => maxK j (mem_univ _))
          (by omega) (Or.inl large)⟩
    have smallK (j : V) : (K j).card ≤ 2 := by
      have := maxK j (mem_univ _)
      omega
    by_cases asymm : ∃ i j : V, j ∈ K i ∧ j ≠ i ∧ {j} ∈ C
    · obtain ⟨i,j,hj,ne,hjC⟩ := asymm
      have two : 2 ≤ (K i).card := by
        have sub : ({j,i} : Finset V) ⊆ K i := by simp [insert_subset_iff,hj,(core i).2.1]
        simpa [ne] using card_le_card sub
      exact ⟨i,point i fun T ht =>
        complement_injection bot K core i T (small T ht) (fun a => (smallK a).trans two)
          two (Or.inr ⟨j,hj,ne,hjC⟩)⟩
    have symm (i j : V) (hj : j ∈ K i) : K j = K i := by
      by_cases e : j = i
      · subst j; rfl
      have inc := (core j).2.2 _ (core i).1 hj
      have two : 2 ≤ (K j).card := by
        have nc : (K j).card ≠ 0 := Nat.ne_of_gt (card_pos.mpr ⟨j,(core j).2.1⟩)
        have no : (K j).card ≠ 1 := by
          intro one
          obtain ⟨a,ha⟩ := card_eq_one.mp one
          have ja : j = a := mem_singleton.mp (ha ▸ (core j).2.1)
          subst a
          exact asymm ⟨i,j,hj,e,ha ▸ (core j).1⟩
        omega
      exact eq_of_subset_of_card_le inc ((smallK i).trans two)
    obtain ⟨P,hn,hm⟩ := symmetric_mass (fun Q bot _ U sing ub => fourth_mass_of_singletons Q bot U sing ub) C bot cl K core symm
    obtain ⟨i,good⟩ := averaged P hn W w nn (fun T ht => hm T (small T ht))
    refine ⟨i,sub_nonneg.mp ?_⟩
    rw [← sum_sub_distrib]
    convert good using 1
    apply sum_congr rfl
    intro T _
    rw [← mul_sub]
    by_cases hit : i ∈ T <;> simp [hit,balance]
  · obtain ⟨k,nk⟩ := not_forall.mp occ
    refine ⟨k,point k fun T _ => ?_⟩
    have eq : omits C k T = ∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro S hs
      exact nk ⟨S,(mem_filter.mp hs).1,(mem_filter.mp hs).2.2⟩
    simp [eq]

/-- The original Phan inequality at all degrees within four of the ground-set order. -/
theorem phan_fourth [Fintype V] [Nonempty V] (F : Finset (Finset V))
    (top : (univ : Finset V) ∈ F)
    (closed : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)
    (m : ℕ) (near : Fintype.card V ≤ m+4) (x : V → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∃ k : V,
      (∑ A ∈ F.filter (fun A => k ∉ A), ∑ B ∈ A.powersetCard m, ∏ i ∈ B, x i) ≤
      ∑ A ∈ F.filter (fun A => k ∈ A), ∑ B ∈ (A.erase k).powersetCard m, ∏ i ∈ B, x i :=
  phan_of_coefficients F m x
    (weighted_coefficients_of_windows F top closed weighted_fourth m near x hx)

#print axioms weighted_fourth
#print axioms phan_fourth
end UnionClosedBoundary
