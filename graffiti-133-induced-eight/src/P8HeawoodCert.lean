import P8HeawoodCertBase

namespace Graffiti133P8Heawood
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000

private def anchorOne (i : Fin 9) : Cert 10 :=
  match i.val with
  | 0 => .eight ![2,3,4,5,6,8,0,9]
  | 1 => .eight ![3,4,5,6,8,0,1,9]
  | 2 => .eight ![0,8,6,5,4,3,2,9]
  | 3 => .eight ![1,0,8,6,5,4,3,9]
  | 4 => .eight ![2,1,0,8,6,5,4,9]
  | 5 => .eight ![3,2,1,0,8,6,5,9]
  | 6 => .eight ![0,1,2,3,4,5,6,9]
  | 7 => .pass
  | 8 => .eight ![1,2,3,4,5,6,8,9]
  | _ => .pass
private def anchorTwo (i j : Fin 9) : Cert 10 :=
  match i.val,j.val with
  | 0, 1 => .eight ![2,3,4,5,6,8,0,9]
  | 0, 7 => .eight ![2,3,4,5,6,8,0,9]
  | 0, 8 => .eight ![1,2,3,4,5,6,8,9]
  | 1, 2 => .eight ![0,8,6,5,4,3,2,9]
  | 1, 5 => .pass
  | 2, 3 => .eight ![1,0,8,6,5,4,3,9]
  | 2, 6 => .pass
  | 3, 4 => .eight ![2,1,0,8,6,5,4,9]
  | 3, 8 => .pass
  | 4, 5 => .eight ![3,2,1,0,8,6,5,9]
  | 4, 7 => .eight ![2,1,0,8,6,5,4,9]
  | 5, 6 => .eight ![2,3,4,7,0,8,6,9]
  | 6, 8 => .eight ![0,1,2,3,4,5,6,9]
  | _, _ => .pass
private def heawoodOne (i : Fin 14) : Cert 15 :=
  match i.val with
  | 0 => .eight ![2,3,4,5,6,8,0,14]
  | 1 => .eight ![3,4,5,6,8,0,1,14]
  | 2 => .eight ![0,7,4,5,6,10,2,14]
  | 3 => .eight ![1,0,7,11,13,12,3,14]
  | 4 => .eight ![0,1,2,10,6,5,4,14]
  | 5 => .eight ![1,0,7,11,10,6,5,14]
  | 6 => .eight ![0,1,2,3,4,5,6,14]
  | 7 => .eight ![1,2,3,12,13,11,7,14]
  | 8 => .eight ![1,2,3,4,5,6,8,14]
  | 9 => .eight ![0,7,4,3,12,13,9,14]
  | 10 => .eight ![1,0,7,4,5,6,10,14]
  | 11 => .eight ![0,1,2,3,12,13,11,14]
  | 12 => .eight ![0,1,2,10,11,13,12,14]
  | 13 => .eight ![1,0,7,4,3,12,13,14]
  | _ => .pass
private def heawoodTwo (i j : Fin 14) : Cert 15 :=
  match i.val,j.val with
  | 0, 1 => .eight ![2,3,4,5,6,8,0,14]
  | 0, 7 => .eight ![1,2,3,12,13,11,7,14]
  | 0, 8 => .eight ![1,2,3,4,5,6,8,14]
  | 1, 2 => .eight ![0,7,4,5,6,10,2,14]
  | 1, 9 => .eight ![0,7,4,3,12,13,9,14]
  | 2, 3 => .eight ![0,7,4,5,6,10,2,14]
  | 2, 10 => .eight ![0,7,11,13,12,3,2,14]
  | 3, 4 => .eight ![0,1,2,10,6,5,4,14]
  | 3, 12 => .eight ![0,1,2,10,11,13,12,14]
  | 4, 5 => .eight ![0,1,9,13,12,3,4,14]
  | 4, 7 => .eight ![0,1,2,10,6,5,4,14]
  | 5, 6 => .eight ![0,1,9,13,11,10,6,14]
  | 5, 9 => .eight ![0,7,4,3,12,13,9,14]
  | 6, 8 => .eight ![0,1,2,3,4,5,6,14]
  | 6, 10 => .eight ![0,1,2,3,4,5,6,14]
  | 7, 11 => .eight ![0,1,2,3,12,13,11,14]
  | 8, 12 => .eight ![0,1,2,10,11,13,12,14]
  | 9, 13 => .eight ![0,7,11,10,6,5,9,14]
  | 10, 11 => .eight ![0,1,2,3,12,13,11,14]
  | 11, 13 => .eight ![0,1,9,5,6,10,11,14]
  | 12, 13 => .eight ![0,1,9,5,4,3,12,14]
  | _, _ => .pass
private def pairCert (i j : Fin 4) (e : Bool) : Cert 11 :=
  match i.val,j.val,e with
  | 0, 0, false => .four 1 5 9 10
  | 0, 0, true => .four 1 5 9 10
  | 0, 1, false => .pass
  | 0, 1, true => .four 1 10 2 9
  | 0, 2, false => .pass
  | 0, 2, true => .five ![0,1,9,10,7]
  | 0, 3, false => .pass
  | 0, 3, true => .five ![0,1,9,10,8]
  | 1, 0, false => .pass
  | 1, 0, true => .four 1 9 2 10
  | 1, 1, false => .four 2 6 9 10
  | 1, 1, true => .four 2 6 9 10
  | 1, 2, false => .eight ![1,2,9,6,5,4,7,10]
  | 1, 2, true => .pass
  | 1, 3, false => .pass
  | 1, 3, true => .four 2 10 3 9
  | 2, 0, false => .pass
  | 2, 0, true => .five ![0,1,10,9,7]
  | 2, 1, false => .eight ![1,2,10,6,5,4,7,9]
  | 2, 1, true => .pass
  | 2, 2, false => .pass
  | 2, 2, true => .pass
  | 2, 3, false => .pass
  | 2, 3, true => .five ![0,7,9,10,8]
  | 3, 0, false => .pass
  | 3, 0, true => .five ![0,1,10,9,8]
  | 3, 1, false => .pass
  | 3, 1, true => .four 2 9 3 10
  | 3, 2, false => .pass
  | 3, 2, true => .five ![0,7,10,9,8]
  | 3, 3, false => .four 3 8 9 10
  | 3, 3, true => .four 3 8 9 10
  | _, _, _ => .pass
private def coreCert (m : Fin 16) : Cert 14 :=
  match m.val with
  | 1 => .eight ![0,7,11,10,6,5,9,13]
  | 2 => .eight ![1,0,7,4,5,6,10,13]
  | 3 => .five ![1,2,10,13,9]
  | 4 => .eight ![0,1,9,5,6,10,11,13]
  | 5 => .eight ![0,8,12,3,2,10,11,13]
  | 6 => .eight ![1,0,7,4,5,6,10,13]
  | 7 => .five ![1,2,10,13,9]
  | 8 => .eight ![0,1,9,5,4,3,12,13]
  | 9 => .eight ![0,7,11,10,2,3,12,13]
  | 10 => .five ![2,3,12,13,10]
  | 11 => .five ![1,2,10,13,9]
  | 12 => .eight ![0,1,9,5,4,3,12,13]
  | 13 => .pass
  | 14 => .five ![2,3,12,13,10]
  | 15 => .five ![1,2,10,13,9]
  | _ => .pass

private def One {n : ℕ} (i k : Fin n) : Bool := decide (k=i)
private def Two {n : ℕ} (i j k : Fin n) : Bool := decide (k=i ∨ k=j)
private def AnchorSparse : Fin 9 → Fin 9 → Prop :=
  edgeRel (edgeAnchor ++ [(1,5),(2,6),(3,8)])
private instance : DecidableRel AnchorSparse :=
  inferInstanceAs (DecidableRel (edgeRel (edgeAnchor ++ [(1,5),(2,6),(3,8)])))

private lemma sparse_contacts {n : ℕ} {R S : Fin n → Fin n → Prop} {b : Fin n → Bool}
    (hg : Good (ext R b)) (symm : ∀ i j, R i j → R j i) (hs : ∀ i j, R i j → i≠j)
    (cover : ∀ i j, i≠j → ¬S i j → Short R i j)
    (tri : ∀ i j k, S i j → S i k → S j k → False) (contact : ∃ i,b i=true) :
    (∃ i, b=One i) ∨ ∃ i j, i < j ∧ S i j ∧ b=Two i j := by
  classical
  have allows (i j) (ij : i≠j) (hi : b i=true) (hj : b j=true) : S i j := by
    by_contra no
    exact no_short hg symm hs ij hi hj (cover i j ij no)
  obtain ⟨i,hi⟩ := contact
  by_cases other : ∃ j, i≠j ∧ b j=true
  · obtain ⟨j,ij,hj⟩ := other
    have all (k) (hk : b k=true) : k=i ∨ k=j := by
      by_contra no
      push_neg at no
      exact tri i j k (allows i j ij hi hj)
        (allows i k no.1.symm hi hk) (allows j k no.2.symm hj hk)
    have eq : b=Two i j := by
      funext k
      by_cases h : k=i ∨ k=j
      · rw [show Two i j k=true by simp [Two,h]]
        rcases h with rfl | rfl <;> assumption
      · cases hk : b k
        · simp [Two,h]
        · exact (h (all _ hk)).elim
    rcases lt_or_gt_of_ne ij with lt | gt
    · exact Or.inr ⟨i,j,lt,allows i j ij hi hj,eq⟩
    · refine Or.inr ⟨j,i,gt,allows j i ij.symm hj hi,eq.trans ?_⟩
      funext k
      simp [Two,or_comm]
  · apply Or.inl
    refine ⟨i,?_⟩
    funext k
    by_cases h : k=i
    · simpa [One,h] using (h.symm ▸ hi : b k=true)
    · cases hk : b k
      · simp [One,h]
      · exact (other ⟨k,fun e => h e.symm,hk⟩).elim

private instance {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] : DecidableRel (Short R) := by
  intro i j
  unfold Short
  infer_instance

private lemma anchorSymm : ∀ i j, Anchor i j → Anchor j i := by decide
private lemma anchorLoop : ∀ i j, Anchor i j → i≠j := by decide
private lemma anchorCover : ∀ i j, i≠j → ¬AnchorSparse i j → Short Anchor i j := by decide
private lemma anchorTri : ∀ i j k, AnchorSparse i j → AnchorSparse i k → AnchorSparse j k → False := by decide
private lemma hwSymm : ∀ i j, Heawood i j → Heawood j i := by decide
private lemma hwLoop : ∀ i j, Heawood i j → i≠j := by decide
private lemma hwCover : ∀ i j, i≠j → ¬Heawood i j → Short Heawood i j := by decide
private lemma hwTri : ∀ i j k, Heawood i j → Heawood i k → Heawood j k → False := by decide

private lemma anchorOneChecked : ∀ i,
    (anchorOne i).Valid (ext Anchor (One i)) (∃ t, ∀ k, One i k=Profile t k) := by decide
private lemma anchorTwoChecked : ∀ i j, i < j → AnchorSparse i j →
    (anchorTwo i j).Valid (ext Anchor (Two i j)) (∃ t, ∀ k, Two i j k=Profile t k) := by decide
private lemma hwOneChecked : ∀ i, (heawoodOne i).Valid (ext Heawood (One i)) False := by decide
private lemma hwTwoChecked : ∀ i j, i < j → Heawood i j →
    (heawoodTwo i j).Valid (ext Heawood (Two i j)) False := by decide
private lemma pairChecked : ∀ i j e, (pairCert i j e).Valid (AnchorPair i j e) (AllowedPair i j e) := by decide

def FromMask (m : Fin 16) (i : Fin 4) : Bool := m.val.testBit i.val

private lemma maskCoverage : ∀ b : Fin 4 → Bool, ∃ m, ∀ i, FromMask m i = b i := by decide
private lemma coreChecked : ∀ m : Fin 16, (∃ i, FromMask m i = true) →
  (coreCert m).Valid (ext Core (CoreMask (FromMask m))) (∀ i, FromMask m i=FarProfile i) := by decide

theorem anchor_contacts (b : Fin 9 → Bool) (hg : Good (ext Anchor b))
    (nonempty : ∃ i,b i=true) : ∃ t, ∀ i,b i=Profile t i := by
  rcases sparse_contacts hg anchorSymm anchorLoop anchorCover anchorTri nonempty with
    ⟨i,rfl⟩ | ⟨i,j,ij,allow,rfl⟩
  · exact (anchorOne i).sound (anchorOneChecked i) hg
  · exact (anchorTwo i j).sound (anchorTwoChecked i j ij allow) hg

theorem pair_contacts (i j : Fin 4) (e : Bool) (hg : Good (AnchorPair i j e)) :
    AllowedPair i j e :=
  (pairCert i j e).sound (pairChecked i j e) hg

theorem core_contacts (b : Fin 4 → Bool) (hg : Good (ext Core (CoreMask b)))
    (nonempty : ∃ i,b i=true) : ∀ i,b i=FarProfile i := by
  obtain ⟨m,hm⟩ := maskCoverage b
  have em : FromMask m=b := funext hm
  subst b
  exact (coreCert m).sound (coreChecked m nonempty) hg

theorem heawood_no_contacts (b : Fin 14 → Bool) (hg : Good (ext Heawood b)) :
    ∀ i,b i=false := by
  intro i
  cases hi : b i
  · rfl
  · exfalso
    rcases sparse_contacts hg hwSymm hwLoop hwCover hwTri ⟨i,hi⟩ with
      ⟨j,rfl⟩ | ⟨j,k,jk,allow,rfl⟩
    · exact (heawoodOne j).sound (hwOneChecked j) hg
    · exact (heawoodTwo j k).sound (hwTwoChecked j k jk allow) hg

theorem avoid_far_type_one :
    ¬ Good (ext (ext Anchor (Profile (1:Fin 4))) (fun k : Fin 10 => decide (k=Fin.last 9))) := by
  intro hg
  let c : Cert 11 := .eight ![1,0,7,4,5,6,9,10]
  exact c.sound (by decide) hg

#print axioms avoid_far_type_one
#print axioms anchor_contacts
#print axioms pair_contacts
#print axioms core_contacts
#print axioms heawood_no_contacts

end Graffiti133P8Heawood
