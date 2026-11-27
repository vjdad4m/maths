import WidePlacement

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph CompactOmission

structure Family (n : ℕ) where
  fixedBits : Fin (n+1) → ℕ
  choices : List (Fin (n+1) × Fin (n+1))

def Family.pattern {n : ℕ} (d : Family n) : Pattern (n+1) where
  fixed i j := (d.fixedBits i).testBit j.val
  slot i j :=
    letI : BEq (Fin (n+1) × Fin (n+1)) := instBEqOfDecidableEq
    let ix := d.choices.idxOf (min i j,max i j)
    if ix < d.choices.length then some ix else none

def Must {n : ℕ} (b : Layout n) (i j : Fin (n+1)) : Prop :=
  (i.val+1 = j.val ∧ j.val < n) ∨ (i = Fin.last n ∧ j ∈ b.ports)

instance {n : ℕ} (b : Layout n) (i j : Fin (n+1)) : Decidable (Must b i j) := by
  unfold Must
  infer_instance

def Off {n : ℕ} (b : Layout n) (m : Fin 3) (i j : Fin (n+1)) : Prop :=
  i = j ∨
  (i ∈ b.ports ∧ j ∈ b.ports) ∨ (i ∈ b.lefts ∧ j ∈ b.lefts) ∨
  (i ∈ b.rights ∧ j ∈ b.rights) ∨ (i = Fin.last n ∧ j ∉ b.ports) ∨
  (i = b.port m ∧ j ∉ b.mateContacts m)

instance {n : ℕ} (b : Layout n) (m : Fin 3) (i j : Fin (n+1)) : Decidable (Off b m i j) := by
  unfold Off
  infer_instance

def Consistent {n : ℕ} (b : Layout n) (m : Fin 3) (d : Family n) : Prop :=
  ∀ i j, d.pattern.slot i j = none →
    if d.pattern.fixed i j then Must b i j ∨ Must b j i else Off b m i j ∨ Off b m j i

instance {n : ℕ} (b : Layout n) (m : Fin 3) (d : Family n) : Decidable (Consistent b m d) := by
  unfold Consistent
  infer_instance

variable {V : Type*} {G : SimpleGraph V}

theorem Placement.must {n : ℕ} {b : Layout n} {m : Fin 3} {f : Fin (n+1) ↪ V}
    (P : Placement G f b m) {i j} (h : Must b i j) : G.Adj (f i) (f j) := by
  rcases h with ⟨e,l⟩|⟨rfl,port⟩
  · exact P.consecutive _ _ e l
  · exact (P.omission _).mpr port

theorem Placement.off {n : ℕ} {b : Layout n} {m : Fin 3} {f : Fin (n+1) ↪ V}
    (P : Placement G f b m) {i j} (h : Off b m i j) : ¬ G.Adj (f i) (f j) := by
  rcases h with rfl|⟨hi,hj⟩|⟨hi,hj⟩|⟨hi,hj⟩|⟨rfl,hj⟩|⟨rfl,hj⟩
  · exact G.loopless _
  · exact P.portOff _ hi _ hj
  · exact P.leftOff _ hi _ hj
  · exact P.rightOff _ hi _ hj
  · exact fun ha => hj ((P.omission _).mp ha)
  · exact fun ha => hj (P.mate _ ha)

theorem actual_row [DecidableRel G.Adj] {n : ℕ} {b : Layout n} {m : Fin 3} {f : Fin (n+1) ↪ V}
    (P : Placement G f b m) {d : Family n} (h : Consistent b m d) :
    ∃ row, ∀ i j, G.Adj (f i) (f j) ↔ d.pattern.edge row i j = true := by
  letI : BEq (Fin (n+1) × Fin (n+1)) := instBEqOfDecidableEq
  let flags := fun k : Fin d.choices.length =>
    decide (G.Adj (f (d.choices.get k).1) (f (d.choices.get k).2))
  refine ⟨encode flags,?_⟩
  intro i j
  by_cases hc : (min i j,max i j) ∈ d.choices
  · let k : Fin d.choices.length := ⟨_,List.idxOf_lt_length hc⟩
    have key : d.choices.get k = (min i j,max i j) := by
      exact List.getElem_idxOf (List.idxOf_lt_length hc)
    have same : d.pattern.slot i j = some k.val := by
      simp only [Family.pattern,k,dif_pos k.isLt,if_pos k.isLt]
    simp only [Pattern.edge,same,encode_bit flags k]
    change G.Adj (f i) (f j) ↔ decide (G.Adj (f (d.choices.get k).1) (f (d.choices.get k).2)) = true
    rw [key,decide_eq_true_eq]
    rcases le_total i j with hi|hj
    · rw [min_eq_left hi,max_eq_right hi]
    · rw [min_eq_right hj,max_eq_left hj,G.adj_comm]
  · have none : d.pattern.slot i j = none := by simp [Family.pattern,List.idxOf_eq_length hc]
    rw [Pattern.edge,none]
    have rule := h i j none
    cases e : d.pattern.fixed i j with
    | false =>
      simp only [e,Bool.false_eq_true,if_false] at rule
      exact iff_of_false (rule.elim P.off (fun eq adj => P.off eq adj.symm)) Bool.false_ne_true
    | true =>
      simp only [e,if_true] at rule
      exact iff_of_true (rule.elim P.must (fun eq => (P.must eq).symm)) rfl

def FullyKnown {n : ℕ} (d : Family n) (good : List ℕ) (dom val tag : ℕ) : Prop :=
  tag ∈ good ∧ val = tag ∧ ∀ i j, d.pattern.known dom i j = true

instance {n : ℕ} (d : Family n) (good : List ℕ) (dom val tag : ℕ) :
    Decidable (FullyKnown d good dom val tag) := by unfold FullyKnown; infer_instance

theorem classified {n : ℕ} {d : Family n} {good : List ℕ} {C : Cover (n+1)}
    (pass : C.Valid d.pattern (FullyKnown d good) 0 0) (row : ℕ) :
    (∃ T, SixTree (d.pattern.edge row) T) ∨
      ∃ tag ∈ good, ∀ i j, d.pattern.edge row i j = d.pattern.edge tag i j := by
  rcases Cover.start pass row with tree|⟨dom,val,tag,a,ok,eq,all⟩
  · exact Or.inl tree
  · subst val
    exact Or.inr ⟨tag,ok,fun _ _ => edge_agree d.pattern a (all _ _)⟩

end Graffiti199Depleted.WiderOmission
