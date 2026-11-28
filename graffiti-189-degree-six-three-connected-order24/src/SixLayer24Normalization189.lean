import SixLayer24CoverMiddle189
import SixJointEqualityBase189

namespace Graffiti189LongestPath
open Finset
open scoped BigOperators

/-- A bounded finite family attaining the full sum of its cardinal budgets
has full-sized disjoint members. -/
theorem exact_weighted_cover_members {I X : Type*} [DecidableEq I] [DecidableEq X]
    (T : Finset I) (F : I→Finset X) (B : Finset X) (K : I→ℕ)
    (cov : B⊆T.biUnion F) (card : B.card=∑ a∈T,K a)
    (lim : ∀ a∈T,(F a).card≤K a) :
    (∀ a∈T,(F a).card=K a) ∧ (∀ a∈T,∀ b∈T,a≠b → Disjoint (F a) (F b)) := by
  classical
  have cut (a : I) (aT : a∈T) (S : Finset X) (cover : B⊆S∪(T.erase a).biUnion F) :
      K a≤S.card := by
    have h := (card_le_card cover).trans (card_union_le S ((T.erase a).biUnion F))
    have l := card_biUnion_le.trans (sum_le_sum (s:=T.erase a)
      (f:=fun a=>(F a).card) (g:=K) (fun b bt=>lim b (mem_erase.mp bt).2))
    have e := sum_erase_add T K aT
    rw [card,←e] at h
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

noncomputable def singleShort {I : Type*} [DecidableEq I] (k : ℕ) (a b : I) : ℕ :=
  if b=a then k-1 else k

theorem sum_single_short {I : Type*} [DecidableEq I] (T : Finset I) (k : ℕ)
    (pos : 0<k) {a : I} (aT : a∈T) :
    (∑ b∈T,singleShort k a b)+1=T.card*k := by
  have h := sum_erase_add T (singleShort k a) aT
  have c : (∑ b∈T.erase a,singleShort k a b)=(T.erase a).card*k := by
    calc
      _ = ∑ _b∈T.erase a,k := sum_congr rfl (fun b bm=>by simp [singleShort,(mem_erase.mp bm).1])
      _ = _ := by simp
  rw [c,show singleShort k a a=k-1 by simp [singleShort]] at h
  have e := congrArg (fun n : ℕ=>n*k) (card_erase_add_one aT)
  change ((T.erase a).card+1)*k=T.card*k at e
  rw [Nat.add_mul,one_mul] at e
  omega

theorem short_weighted_cover {I X : Type*} [DecidableEq I] [DecidableEq X]
    (T : Finset I) (F : I→Finset X) (B : Finset X) (k : ℕ)
    (pos : 0<k) (cov : B⊆T.biUnion F) (card : B.card+1=T.card*k)
    (lim : ∀ a∈T,(F a).card≤k) {a : I} (aT : a∈T) (short : (F a).card<k) :
    (∀ b∈T,(F b).card=singleShort k a b) ∧
      (∀ a∈T,∀ b∈T,a≠b → Disjoint (F a) (F b)) := by
  apply exact_weighted_cover_members T F B (singleShort k a) cov
  · have s := sum_single_short T k pos aT
    omega
  · intro b bT
    by_cases e : b=a
    · subst b
      simp [singleShort]
      omega
    · simpa [singleShort,e] using lim b bT

theorem overlap_shortened_cover {I X : Type*} [DecidableEq I] [DecidableEq X]
    (T : Finset I) (F : I→Finset X) (B : Finset X) (k : ℕ)
    (pos : 0<k) (cov : B⊆T.biUnion F) (card : B.card+1=T.card*k)
    (full : ∀ a∈T,(F a).card=k)
    {a b : I} (aT : a∈T) (bT : b∈T) (ab : a≠b) {z : X} (za : z∈F a) (zb : z∈F b) :
    let P (i : I) := if i=b then (F i).erase z else F i
    (B⊆T.biUnion P) ∧ (∀ i∈T,(P i).card=singleShort k b i) ∧
      (∀ i∈T,∀ j∈T,i≠j → Disjoint (P i) (P j)) := by
  let P (i : I) := if i=b then (F i).erase z else F i
  have cp : B⊆T.biUnion P := by
    intro y ym
    obtain ⟨j,jT,jy⟩ := mem_biUnion.mp (cov ym)
    by_cases e : j=b
    · subst j
      by_cases f : y=z
      · refine mem_biUnion.mpr ⟨a,aT,?_⟩
        simpa [P,ab,f] using za
      · refine mem_biUnion.mpr ⟨b,bT,?_⟩
        simpa [P] using mem_erase.mpr ⟨f,jy⟩
    · exact mem_biUnion.mpr ⟨j,jT,by simpa [P,e] using jy⟩
  have pp (i : I) (it : i∈T) : (P i).card≤k := by
    by_cases e : i=b
    · subst i
      simp [P,card_erase_of_mem zb,full b bT]
    · simp [P,e,full i it]
  have sh : (P b).card<k := by
    simp [P,card_erase_of_mem zb,full b bT]
    omega
  exact ⟨cp,short_weighted_cover T P B k pos cp card pp bT sh⟩

namespace Layer24Cover
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {x : V}

theorem near_group_cases (L : Layer24Cover G x) :
    let C := Shell G x 3
    let F := Layer25Group G x
    let k := 7-L.T.card
    (C.card=12 ∧ (∀ a∈L.T,(F a).card=k) ∧
      (∀ a∈L.T,∀ b∈L.T,a≠b → Disjoint (F a) (F b))) ∨
    (C.card=11 ∧ ∃ a∈L.T,(∀ b∈L.T,(F b).card=singleShort k a b) ∧
      (∀ i∈L.T,∀ j∈L.T,i≠j → Disjoint (F i) (F j))) ∨
    (C.card=11 ∧ (∀ a∈L.T,(F a).card=k) ∧
      ∃ a∈L.T,∃ b∈L.T,∃ z∈F a,z∈F b ∧ a≠b ∧
        let P (i : V) := if i=b then (F i).erase z else F i
        C⊆L.T.biUnion P ∧ (∀ i∈L.T,(P i).card=singleShort k b i) ∧
          (∀ i∈L.T,∀ j∈L.T,i≠j → Disjoint (P i) (P j))) := by
  classical
  let C := Shell G x 3
  let F := Layer25Group G x
  let k := 7-L.T.card
  have pos : 0<k := by
    have l := L.tSize
    dsimp [k]
    omega
  have mx : L.T.card*k=12 := by
    rcases L.tSize with t|t <;> simp [k,t]
  rcases L.thirdSize with c11|c12
  · change C.card=11 at c11
    have q : C.card+1=L.T.card*k := by rw [c11,mx]
    by_cases h : ∀ i∈L.T,(F i).card=k
    · right
      right
      refine ⟨c11,h,?_⟩
      have nd : ¬∀ i∈L.T,∀ j∈L.T,i≠j→Disjoint (F i) (F j) := by
        intro dis
        have eq := card_biUnion (s:=L.T) (t:=F) (by
          intro i it j jt ij
          exact dis i it j jt ij)
        have h' : ∑ i∈L.T,(F i).card=L.T.card*k := by
          calc
            _ = ∑ _i∈L.T,k := sum_congr rfl h
            _ = _ := by simp
        have sub : L.T.biUnion F⊆C := by
          intro z zm
          obtain ⟨i,iT,zi⟩ := mem_biUnion.mp zm
          exact (mem_inter.mp zi).1
        have lh := card_le_card sub
        rw [eq,h',mx,c11] at lh
        omega
      push_neg at nd
      obtain ⟨a,aT,b,bT,ab,n⟩ := nd
      obtain ⟨z,za,zb⟩ := not_disjoint_iff.mp n
      exact ⟨a,aT,b,bT,z,za,zb,ab,overlap_shortened_cover L.T F C k pos
        L.groupCover q h aT bT ab za zb⟩
    · right
      left
      push_neg at h
      obtain ⟨a,aT,n⟩ := h
      have u := L.groupBound a aT
      change (F a).card≤k at u
      exact ⟨c11,a,aT,short_weighted_cover L.T F C k pos L.groupCover q L.groupBound aT (by omega)⟩
  · left
    refine ⟨c12,?_⟩
    have e : C.card=L.T.card*k := c12.trans mx.symm
    exact exact_cover_members L.T F C k L.groupCover e L.groupBound
end Layer24Cover

#print axioms Layer24Cover.near_group_cases
end Graffiti189LongestPath
