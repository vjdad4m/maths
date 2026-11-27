import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

namespace FourOrder14Three
open Finset
abbrev Bits := Fin 6 → Bool

def dir (m : Bits) (e f g s t : Bool) (u v : Fin 14) : Bool :=
  let a := u.val
  let b := v.val
  (decide (b=a+1 ∧ b≤10)) ||
  (decide ((a=1 ∨ a=9) ∧ (b=11 ∨ b=12))) ||
  (decide (11≤a ∧ a<b)) ||
  (decide (a=1 ∧ b=13) && s) ||
  (decide (a=9 ∧ b=13) && t) ||
  (if h : a=0 ∧ 3≤b ∧ b≤8 then m ⟨b-3,by omega⟩ else false) ||
  (if h : b=10 ∧ 2≤a ∧ a≤7 then !(m ⟨a-2,by omega⟩) else false) ||
  (decide (a=1 ∧ b=9) && e) ||
  (decide (a=1 ∧ b=8) && f) ||
  (decide (a=2 ∧ b=9) && g)

def edge (m : Bits) (e f g s t : Bool) (u v : Fin 14) : Bool :=
  dir m e f g s t u v || dir m e f g s t v u

def d2Set (m : Bits) (e f g s t : Bool) (x : Fin 14) : Finset (Fin 14) :=
  univ.filter fun y =>
    y≠x ∧ !(edge m e f g s t x y) = true ∧ ∃ z : Fin 14, edge m e f g s t x z = true ∧ edge m e f g s t z y=true

def bits (b0 b1 b2 b3 b4 b5 : Bool) (k : Fin 6) : Bool :=
  if k.val=0 then b0 else if k.val=1 then b1 else if k.val=2 then b2 else if k.val=3 then b3 else if k.val=4 then b4 else b5


def check (m : Bits) (e f g s t : Bool) : Prop :=
  (univ.filter fun i : Fin 6 => m i=true).card=3 →
  (d2Set m e f g s t 0).card≤4 → (d2Set m e f g s t 1).card≤4 →
  (d2Set m e f g s t 9).card≤4 → (d2Set m e f g s t 10).card≤4 → False

noncomputable instance chk (m : Bits) (e f g s t : Bool) : Decidable (check m e f g s t) := by
  unfold check
  infer_instance

def Row (s t : Bool) : Prop :=
  ∀ b0 b1 b2 b3 b4 b5 e f g : Bool, check (bits b0 b1 b2 b3 b4 b5) e f g s t

noncomputable instance (s t : Bool) : Decidable (Row s t) := by
  unfold Row
  infer_instance

set_option maxRecDepth 36000
set_option maxHeartbeats 12000000
private theorem row00 : Row false false := by decide
private theorem row01 : Row false true := by decide
private theorem row10 : Row true false := by decide
private theorem row11 : Row true true := by decide

theorem tiny (m : Bits) (e f g s t : Bool) : check m e f g s t := by
  have tt : Row s t := by cases s <;> cases t
    <;> first | exact row00 | exact row01 | exact row10 | exact row11
  have eq : bits (m 0) (m 1) (m 2) (m 3) (m 4) (m 5)=m := by
    funext i
    fin_cases i <;> rfl
  simpa only [eq] using tt (m 0) (m 1) (m 2) (m 3) (m 4) (m 5) e f g

#print axioms tiny
end FourOrder14Three
