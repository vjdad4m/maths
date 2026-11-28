import SixLayer24SlotNumbers189
import SixLayer24LabelBase189
namespace Graffiti189LongestPath.Layer24Numbering

theorem slot_computation (m : Kind) {t c : ℕ} (ht : t=3 ∨ t=4) (hc : c=childCount m) :
    (∀ j : Fin c,owner m t j.val<t ∧ cell m t j.val<childCap m t (owner m t j.val)) ∧
    (∀ j k : Fin c,owner m t j.val=owner m t k.val → cell m t j.val=cell m t k.val → j=k) ∧
    ∀ (i : Fin t) (k : Fin (childCap m t i.val)),∃ j : Fin c,
      owner m t j.val=i.val ∧ cell m t j.val=k.val := by
  have mcase : m=0 ∨ m=1 ∨ m=2 := by
    have lt := m.isLt
    have h : m.val=0 ∨ m.val=1 ∨ m.val=2 := by omega
    rcases h with e|e|e <;> simp [Fin.ext_iff,e]
  rcases ht with rfl|rfl <;> rcases mcase with rfl|rfl|rfl <;> subst c <;> decide

noncomputable def slotEquiv (m : Kind) {t c : ℕ} (ht : t=3 ∨ t=4) (hc : c=childCount m) :
    Fin c ≃ Σ i : Fin t,Fin (childCap m t i.val) := by
  let L := slot_computation m ht hc
  let f (j : Fin c) : Σ i : Fin t,Fin (childCap m t i.val) :=
    ⟨⟨owner m t j.val,(L.1 j).1⟩,⟨cell m t j.val,(L.1 j).2⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    apply L.2.1 a b
    · exact congrArg (fun p => p.1.val) h
    · exact congrArg (fun p => p.2.val) h
  · rintro ⟨i,k⟩
    obtain ⟨j,ij,kj⟩ := L.2.2 i k
    refine ⟨j,?_⟩
    have e : (f j).1=i := Fin.ext ij
    exact Sigma.ext e (by cases e; exact heq_of_eq (Fin.ext kj))

theorem slot_owner (m : Kind) {t c : ℕ} (ht : t=3 ∨ t=4) (hc : c=childCount m) (j : Fin c) :
    ((slotEquiv m ht hc j).1).val=owner m t j.val := rfl

theorem slot_cell (m : Kind) {t c : ℕ} (ht : t=3 ∨ t=4) (hc : c=childCount m) (j : Fin c) :
    ((slotEquiv m ht hc j).2).val=cell m t j.val := rfl

theorem overlap_shared_slot {t : ℕ} (ht : t=3 ∨ t=4) (j : Fin 11) :
    rawSlot 2 t j.val=cap t-1 ↔ owner 2 t j.val=0 ∧ cell 2 t j.val=cap t-1 := by
  revert j
  rcases ht with rfl|rfl <;> decide

theorem positive_child_cap (m : Kind) {t : ℕ} (ht : t=3 ∨ t=4) (i : Fin t) :
    0<childCap m t i.val := by
  unfold childCap cap
  split <;> omega

#print axioms slot_computation
#print axioms slotEquiv
end Graffiti189LongestPath.Layer24Numbering
