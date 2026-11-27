import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

namespace FourOrder13
open Finset

abbrev Marks := Fin 11 → Fin 3
abbrev Vertex := Fin 13

def dir (j : ℕ) (m : Marks) (e f g h : Bool) (u v : Vertex) : Bool :=
  let a := u.val
  let b := v.val
  decide (b=a+1 ∧ b≤11) ||
  decide ((a=1 ∨ a=j) ∧ b=12) ||
  (if q : a=0 ∧ 1≤b ∧ b≤11 then decide (m ⟨b-1,by omega⟩=1) else false) ||
  (if q : b=11 ∧ a<11 then decide (m ⟨a,q.2⟩=2) else false) ||
  (decide (a=1 ∧ b=j) && e) ||
  (decide (a=1 ∧ b=j-1) && f) ||
  (decide (a=2 ∧ b=j) && g) ||
  (decide (j≠10 ∧ a=1 ∧ b=j+1) && h)

def edge (j : ℕ) (m : Marks) (e f g h : Bool) (u v : Vertex) : Bool :=
  dir j m e f g h u v || dir j m e f g h v u

def degree (j : ℕ) (m : Marks) (e f g h : Bool) (u : Vertex) : ℕ :=
  (univ.filter fun v => edge j m e f g h u v=true).card

def d2Set (j : ℕ) (m : Marks) (e f g h : Bool) (u : Vertex) : Finset Vertex :=
  univ.filter fun v => v≠u ∧ !edge j m e f g h u v = true ∧
    ∃ w : Vertex, edge j m e f g h u w=true ∧ edge j m e f g h w v=true

def markCount (m : Marks) (c : Fin 3) : ℕ := (univ.filter fun k => m k=c).card

def winning (k : Fin 11) : Fin 3 :=
  if k.val=0 ∨ 6≤k.val ∧ k.val≤8 then 1
  else if 2≤k.val ∧ k.val≤4 ∨ k.val=10 then 2 else 0

def check (j : ℕ) (m : Marks) (e f g h : Bool) (hj : j<13) : Prop :=
  4≤markCount m 1 → 4≤markCount m 2 →
  4≤degree j m e f g h 1 → 4≤degree j m e f g h ⟨j,hj⟩ →
  (d2Set j m e f g h 0).card≤4 →
  (d2Set j m e f g h 1).card≤4 →
  (d2Set j m e f g h ⟨j,hj⟩).card≤4 →
  (d2Set j m e f g h 11).card≤4 →
  (d2Set j m e f g h 12).card≤4 →
  j=10 ∧ e=true ∧ f=true ∧ g=true ∧ ∀ k : Fin 11, m k=winning k

noncomputable instance (j : ℕ) (m : Marks) (e f g h : Bool) (hj : j<13) :
    Decidable (check j m e f g h hj) := by unfold check; infer_instance

/-- Removing the forced marks leaves at most seven slots. The final digit
is unused unless j=10. -/
def coord (j k : ℕ) : Fin 7 :=
  ⟨min 6 (if j<10 ∧ j<k then k-4 else k-2), by omega⟩

def site (j : ℕ) (t : Fin 7) : Fin 11 :=
  ⟨min 10 (if j<10 ∧ j-1≤t.val+2 then t.val+4 else t.val+2), by omega⟩

def decode (j : ℕ) (d : Fin 7 → Fin 3) (k : Fin 11) : Fin 3 :=
  if k.val=0 then 1 else if k.val=10 then 2
  else if k.val=1 ∨ k.val+1=j ∨ k.val=j ∧ j≠10 then 0
  else d (coord j k.val)

private theorem site_coord (j : ℕ) (jl : 4≤j) (jh : j≤10) (k : Fin 11)
    (h0 : k.val≠0) (h10 : k.val≠10)
    (hh : ¬(k.val=1 ∨ k.val+1=j ∨ k.val=j ∧ j≠10)) :
    site j (coord j k.val) = k := by
  have hbound := k.isLt
  have hk1 : k.val≠1 := fun e => hh (.inl e)
  have hgap : k.val+1≠j := fun e => hh (.inr (.inl e))
  have hkJ (h : j<10) : k.val≠j := fun e => hh (.inr (.inr ⟨e,by omega⟩))
  apply Fin.ext
  change min 10 (if j<10 ∧ j-1≤(coord j k.val).val+2
    then (coord j k.val).val+4 else (coord j k.val).val+2) = k.val
  by_cases A : j<10 ∧ j<k.val
  · have B : k.val-4≤6 := by omega
    simp only [coord,Fin.val_mk,if_pos A,min_eq_right B]
    have C : j<10 ∧ j-1≤k.val-4+2 := ⟨A.1,by omega⟩
    rw [if_pos C,show k.val-4+4=k.val by omega,min_eq_right (by omega)]
  · have B : k.val-2≤6 := by
      by_cases J : j<10
      · have N := hkJ J
        omega
      · omega
    simp only [coord,Fin.val_mk,if_neg A,min_eq_right B]
    have C : ¬(j<10 ∧ j-1≤k.val-2+2) := by
      intro E
      have N := hkJ E.1
      omega
    rw [if_neg C,show k.val-2+2=k.val by omega,min_eq_right (by omega)]

theorem decode_complete (j : ℕ) (jl : 4≤j) (jh : j≤10) (m : Marks)
    (h0 : m 0=1) (h10 : m 10=2) (h1 : m 1=0)
    (hj1 : ∀ k : Fin 11, k.val+1=j → m k=0)
    (hj : ∀ k : Fin 11, k.val=j → j≠10 → m k=0) :
    decode j (fun t => m (site j t)) = m := by
  funext k
  unfold decode
  split
  next a =>
    have ek : k=(0:Fin 11) := Fin.ext a
    simpa only [ek] using h0.symm
  next a =>
    split
    next b =>
      have ek : k=(10:Fin 11) := Fin.ext b
      simpa only [ek] using h10.symm
    next b =>
      split
      next h =>
        rcases h with l|l|⟨l,n⟩
        · have ek : k=(1:Fin 11) := Fin.ext l
          simpa only [ek] using h1.symm
        · exact (hj1 k l).symm
        · exact (hj k l n).symm
      next h =>
        exact congrArg m (site_coord j jl jh k a b h)

def admissible (j : ℕ) (m : Marks) (e f g h : Bool) (hj : j<13) : Bool :=
  decide (4≤markCount m 1) && decide (4≤markCount m 2) &&
    decide (4≤degree j m e f g h 1) && decide (4≤degree j m e f g h ⟨j,hj⟩) &&
    decide ((d2Set j m e f g h 0).card≤4) &&
    decide ((d2Set j m e f g h 1).card≤4) &&
    decide ((d2Set j m e f g h ⟨j,hj⟩).card≤4) &&
    decide ((d2Set j m e f g h 11).card≤4) &&
    decide ((d2Set j m e f g h 12).card≤4)

def success (j : ℕ) (m : Marks) (e f g : Bool) : Bool :=
  decide (j=10) && e && f && g && decide (∀ k : Fin 11, m k=winning k)

def allBits : ℕ → List (List Bool)
  | 0 => [[]]
  | n+1 => (allBits n).map (false :: ·) ++ (allBits n).map (true :: ·)

def allDigits : ℕ → List (List (Fin 3))
  | 0 => [[]]
  | n+1 => (allDigits n).map ((0 : Fin 3) :: ·) ++
    (allDigits n).map ((1 : Fin 3) :: ·) ++ (allDigits n).map ((2 : Fin 3) :: ·)

def evalModel (j : ℕ) (hj : j<13) (d : List (Fin 3)) (flags : List Bool) : Bool :=
  let m := decode j (fun k => (d[k.val]?).getD 0)
  let g := fun i : ℕ => (flags[i]?).getD false
  !admissible j m (g 0) (g 1) (g 2) (g 3) hj || success j m (g 0) (g 1) (g 2)


def proposedMarks (j : ℕ) (d : List (Fin 3)) : Marks :=
  decode j (fun k => (d[k.val]?).getD 0)


def TableShard (j : ℕ) (hj : j<13) (a b c : Fin 3) :=
  (allDigits (if j=10 then 4 else 3)).all (fun tail =>
    let d := a::b::c::tail
    if 4≤markCount (proposedMarks j d) 1 ∧ 4≤markCount (proposedMarks j d) 2 then
      (allBits 4).all (evalModel j hj d)
    else true) = true

def Table (j : ℕ) (hj : j<13) : Prop := ∀ a b c : Fin 3, TableShard j hj a b c

end FourOrder13
