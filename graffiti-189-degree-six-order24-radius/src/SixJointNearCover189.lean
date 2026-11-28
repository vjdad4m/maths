import SixJointNearEquality189

namespace Graffiti189LongestPath
open Finset

theorem label_three_of_mem {I : Type*} [DecidableEq I] {T : Finset I}
    (t3 : T.card=3) {a b : I} (aT : a∈T) (bT : b∈T) (ab : a≠b) :
    ∃ c∈T,c≠a ∧ c≠b ∧ T={a,b,c} := by
  have v : (T.erase a).card=2 := by rw [card_erase_of_mem aT,t3]
  have bh : b∈T.erase a := mem_erase.mpr ⟨ab.symm,bT⟩
  have u : ((T.erase a).erase b).card=1 := by rw [card_erase_of_mem bh,v]
  obtain ⟨c,cm⟩ := card_pos.mp (show 0<((T.erase a).erase b).card by omega)
  obtain ⟨cb,cm'⟩ := mem_erase.mp cm
  obtain ⟨ca,cT⟩ := mem_erase.mp cm'
  refine ⟨c,cT,ca,cb,?_⟩
  symm
  apply eq_of_subset_of_card_le
    (insert_subset_iff.mpr ⟨aT,insert_subset_iff.mpr ⟨bT,singleton_subset_iff.mpr cT⟩⟩)
  rw [card_insert_of_not_mem (by simp [ab,ca.symm]),card_insert_of_not_mem (by simp [cb.symm]),card_singleton,t3]

theorem biUnion_three {I X : Type*} [DecidableEq I] [DecidableEq X] (F : I→Finset X)
    {a b c : I} : ({a,b,c}:Finset I).biUnion F=F a∪F b∪F c := by
  ext z
  simp only [mem_biUnion,mem_insert,mem_singleton,mem_union]
  constructor
  · rintro ⟨w,hw,z⟩
    rcases hw with rfl|rfl|rfl
    · exact Or.inl (Or.inl z)
    · exact Or.inl (Or.inr z)
    · exact Or.inr z
  · rintro ((z|z)|z)
    · exact ⟨a,Or.inl rfl,z⟩
    · exact ⟨b,Or.inr (Or.inl rfl),z⟩
    · exact ⟨c,Or.inr (Or.inr rfl),z⟩

theorem near_cover_deficient_members {I X : Type*} [DecidableEq I] [DecidableEq X]
    (T : Finset I) (F : I→Finset X) (U : Finset X)
    (t3 : T.card=3) (cov : U⊆T.biUnion F) (u11 : 11≤U.card)
    (small : ∀ i∈T,(F i).card≤4) {a : I} (aT : a∈T) (a3 : (F a).card<4) :
    (F a).card=3 ∧ (∀ b∈T,b≠a → (F b).card=4) ∧
      (∀ i∈T,∀ j∈T,i≠j → Disjoint (F i) (F j)) := by
  classical
  have upper {b c : I} (bT : b∈T) (cT : c∈T) (labels : T={a,b,c}) :
      (F a).card=3 ∧ (F b).card=4 ∧ (F c).card=4 ∧
      Disjoint (F a) (F b) ∧ Disjoint (F a∪F b) (F c) := by
    have low := u11.trans (card_le_card cov)
    rw [labels,biUnion_three] at low
    have ea := card_union_add_card_inter (F a) (F b)
    have eb := card_union_add_card_inter (F a∪F b) (F c)
    have bb := small b bT
    have cc := small c cT
    exact ⟨by omega,by omega,by omega,
      disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp (by omega)),
      disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp (by omega))⟩
  have sub : (T.erase a).card=2 := by rw [card_erase_of_mem aT,t3]
  obtain ⟨b,bm⟩ := card_pos.mp (show 0<(T.erase a).card by omega)
  obtain ⟨c,cT,_,_,labels⟩ := label_three_of_mem t3 aT (mem_erase.mp bm).2 (mem_erase.mp bm).1.symm
  obtain ⟨aE,bE,cE,ab,cc⟩ := upper (mem_erase.mp bm).2 cT labels
  have ac : Disjoint (F a) (F c) := cc.mono_left subset_union_left
  have bc : Disjoint (F b) (F c) := cc.mono_left subset_union_right
  have classify : ∀ i∈T,i=a ∨ i=b ∨ i=c := fun i im=>by simpa only [labels,mem_insert,mem_singleton] using im
  refine ⟨aE,?_,?_⟩
  · intro i im ia
    rcases classify i im with eq|rfl|rfl
    · exact False.elim (ia eq)
    · exact bE
    · exact cE
  · intro i im j jm ij
    rcases classify i im with rfl|rfl|rfl <;> rcases classify j jm with rfl|rfl|rfl
    · exact False.elim (ij rfl)
    · exact ab
    · exact ac
    · exact ab.symm
    · exact False.elim (ij rfl)
    · exact bc
    · exact ac.symm
    · exact bc.symm
    · exact False.elim (ij rfl)

theorem near_cover_not_common_to_three {I X : Type*} [DecidableEq I] [DecidableEq X]
    (T : Finset I) (F : I→Finset X) (U : Finset X)
    (t3 : T.card=3) (cov : U⊆T.biUnion F) (u11 : 11≤U.card)
    (small : ∀ i∈T,(F i).card≤4) {z : X} (_zu : z∈U)
    {a b c : I} (aT : a∈T) (bT : b∈T) (cT : c∈T)
    (ab : a≠b) (ac : a≠c) (bc : b≠c) (za : z∈F a) (zb : z∈F b) (zc : z∈F c) : False := by
  classical
  have labels : T={a,b,c} := by
    symm
    apply eq_of_subset_of_card_le
      (insert_subset_iff.mpr ⟨aT,insert_subset_iff.mpr ⟨bT,singleton_subset_iff.mpr cT⟩⟩)
    rw [card_insert_of_not_mem (by simp [ab,ac]),card_insert_of_not_mem (by simp [bc]),card_singleton,t3]
  have low := u11.trans (card_le_card cov)
  rw [labels,biUnion_three] at low
  have ea := card_union_add_card_inter (F a) (F b)
  have eb := card_union_add_card_inter (F a∪F b) (F c)
  have n1 : 1≤(F a∩F b).card := card_pos.mpr ⟨z,mem_inter.mpr ⟨za,zb⟩⟩
  have n2 : 1≤((F a∪F b)∩F c).card := card_pos.mpr
    ⟨z,mem_inter.mpr ⟨mem_union_left _ za,zc⟩⟩
  have aa := small a aT
  have bb := small b bT
  have cc := small c cT
  omega

#print axioms near_cover_deficient_members
#print axioms near_cover_not_common_to_three
end Graffiti189LongestPath
