import CompactGraphLifts
import Mathlib.Data.Nat.BinaryRec

namespace Graffiti199Depleted.WiderOmission

open CompactOmission (SixTree)

def encode : {n : ℕ} → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n+1, f => Nat.bit (f 0) (encode (n := n) (fun i => f i.succ))

theorem encode_bit {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (encode f).testBit i.val = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Nat.testBit_bit_zero _ _
    · change (Nat.bit _ _).testBit (j.val+1) = f j.succ
      rw [Nat.testBit_succ,Nat.bit_div_two]
      exact ih _ j

structure Pattern (n : ℕ) where
  fixed : Fin n → Fin n → Bool
  slot : Fin n → Fin n → Option ℕ

def Pattern.edge {n : ℕ} (p : Pattern n) (row : ℕ) (i j : Fin n) : Bool :=
  match p.slot i j with
  | none => p.fixed i j
  | some b => row.testBit b

def Pattern.known {n : ℕ} (p : Pattern n) (dom : ℕ) (i j : Fin n) : Bool :=
  match p.slot i j with
  | none => true
  | some b => dom.testBit b

def Agree (row dom value : ℕ) : Prop :=
  ∀ b, dom.testBit b = true → row.testBit b = value.testBit b

theorem edge_agree {n : ℕ} (p : Pattern n) {row dom value : ℕ}
    (a : Agree row dom value) {i j : Fin n} (known : p.known dom i j = true) :
    p.edge row i j = p.edge value i j := by
  cases h : p.slot i j with
  | none => simp [Pattern.edge,h]
  | some b =>
    simpa only [Pattern.edge,h] using a b (by simpa only [Pattern.known,h] using known)

inductive Cover (n : ℕ)
  | split (bit : ℕ) (no yes : Cover n)
  | tree (order : Fin 6 → Fin n)
  | other (tag : ℕ)

def Cover.Valid {n : ℕ} (p : Pattern n) (other : ℕ → ℕ → ℕ → Prop)
    (dom value : ℕ) : Cover n → Prop
  | .split b lo hi =>
      value.testBit b = false ∧
        Valid p other (dom ||| 2^b) value lo ∧
        Valid p other (dom ||| 2^b) (value ||| 2^b) hi
  | .tree T =>
      SixTree (p.edge value) T ∧ ∀ i j, p.known dom (T i) (T j) = true
  | .other tag => other dom value tag

def Cover.decValid {n : ℕ} (p : Pattern n) (other : ℕ → ℕ → ℕ → Prop)
    [∀ d v t, Decidable (other d v t)] (d v : ℕ) (C : Cover n) :
    Decidable (C.Valid p other d v) :=
  match C with
  | .split b lo hi => by
    letI := decValid p other (d ||| 2^b) v lo
    letI := decValid p other (d ||| 2^b) (v ||| 2^b) hi
    exact inferInstanceAs (Decidable (_ = false ∧ _ ∧ _))
  | .tree T => by
    unfold Cover.Valid
    infer_instance
  | .other t => by
    unfold Cover.Valid
    infer_instance

instance {n : ℕ} (p : Pattern n) (other : ℕ → ℕ → ℕ → Prop)
    [∀ d v t, Decidable (other d v t)] (d v : ℕ) (C : Cover n) :
    Decidable (C.Valid p other d v) := Cover.decValid p other d v C

theorem Cover.sound {n : ℕ} {p : Pattern n} {other : ℕ → ℕ → ℕ → Prop}
    {C : Cover n} {row dom value : ℕ} (v : C.Valid p other dom value)
    (a : Agree row dom value) :
    (∃ T, SixTree (p.edge row) T) ∨
      ∃ d x t, Agree row d x ∧ other d x t := by
  induction C generalizing dom value with
  | other t =>
    exact Or.inr ⟨dom,value,t,a,v⟩
  | tree T =>
    obtain ⟨six,known⟩ := v
    have eq (i j : Fin 6) := edge_agree p a (known i j)
    exact Or.inl ⟨T,six.1,fun i hi => by
      obtain ⟨j,e,lt,unique⟩ := six.2 i hi
      exact ⟨j,(eq i j).trans e,lt,fun k h hk => unique k ((eq i k).symm.trans h) hk⟩⟩
  | split b lo hi ihl ihr =>
    obtain ⟨empty,vlo,vhi⟩ := v
    cases h : row.testBit b with
    | false =>
      apply ihl vlo
      intro k hk
      by_cases kb : k = b
      · subst k
        rw [h,empty]
      · apply a k
        simpa [Nat.testBit_two_pow_of_ne (Ne.symm kb)] using hk
    | true =>
      apply ihr vhi
      intro k hk
      by_cases kb : k = b
      · subst k
        simp [h]
      · rw [Nat.testBit_or,Nat.testBit_two_pow_of_ne (Ne.symm kb),Bool.or_false]
        apply a k
        simpa [Nat.testBit_two_pow_of_ne (Ne.symm kb)] using hk

theorem Cover.start {n : ℕ} {p : Pattern n} {other : ℕ → ℕ → ℕ → Prop}
    {C : Cover n} (valid : C.Valid p other 0 0) (row : ℕ) :
    (∃ T, SixTree (p.edge row) T) ∨
      ∃ d x t, Agree row d x ∧ other d x t :=
  sound (row := row) valid (by simp [Agree])

end Graffiti199Depleted.WiderOmission
