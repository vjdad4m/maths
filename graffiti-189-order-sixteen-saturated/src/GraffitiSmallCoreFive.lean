
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

namespace GraffitiSmallCoreFive
open Finset

abbrev Bits := Fin 10 → Bool

def dir (m : Bits) (u v : Fin 5) : Bool :=
  if v.val=1 then m 0
  else if v.val=2 then (if u.val=0 then m 1 else m 2)
  else if v.val=3 then (if u.val=0 then m 3 else if u.val=1 then m 4 else m 5)
  else if v.val=4 then (if u.val=0 then m 6 else if u.val=1 then m 7 else if u.val=2 then m 8 else m 9)
  else false

def edge (m : Bits) (u v : Fin 5) : Bool :=
  if u=v then false else if u.val<v.val then dir m u v else dir m v u

def deg (m : Bits) (a : Fin 5) : ℕ := (univ.filter fun b => edge m a b=true).card

def paths : List (List (Fin 5)) := [
  [0,1,2,3,4],
  [0,1,2,4,3],
  [0,1,3,2,4],
  [0,1,3,4,2],
  [0,1,4,2,3],
  [0,1,4,3,2],
  [0,2,1,3,4],
  [0,2,1,4,3],
  [0,2,3,1,4],
  [0,2,3,4,1],
  [0,2,4,1,3],
  [0,2,4,3,1],
  [0,3,1,2,4],
  [0,3,1,4,2],
  [0,3,2,1,4],
  [0,3,2,4,1],
  [0,3,4,1,2],
  [0,3,4,2,1],
  [0,4,1,2,3],
  [0,4,1,3,2],
  [0,4,2,1,3],
  [0,4,2,3,1],
  [0,4,3,1,2],
  [0,4,3,2,1],
  [1,0,2,3,4],
  [1,0,2,4,3],
  [1,0,3,2,4],
  [1,0,3,4,2],
  [1,0,4,2,3],
  [1,0,4,3,2],
  [1,2,0,3,4],
  [1,2,0,4,3],
  [1,2,3,0,4],
  [1,2,4,0,3],
  [1,3,0,2,4],
  [1,3,0,4,2],
  [1,3,2,0,4],
  [1,3,4,0,2],
  [1,4,0,2,3],
  [1,4,0,3,2],
  [1,4,2,0,3],
  [1,4,3,0,2],
  [2,0,1,3,4],
  [2,0,1,4,3],
  [2,0,3,1,4],
  [2,0,4,1,3],
  [2,1,0,3,4],
  [2,1,0,4,3],
  [2,1,3,0,4],
  [2,1,4,0,3],
  [2,3,0,1,4],
  [2,3,1,0,4],
  [2,4,0,1,3],
  [2,4,1,0,3],
  [3,0,1,2,4],
  [3,0,2,1,4],
  [3,1,0,2,4],
  [3,1,2,0,4],
  [3,2,0,1,4],
  [3,2,1,0,4]]

theorem paths_valid (l : List (Fin 5)) (hl : l∈paths) :
    l.Nodup ∧ (∀ i : Fin 5,i∈l) ∧ l.length=5 := by
  have h : ∀ l∈paths,l.Nodup ∧ (∀ i : Fin 5,i∈l) ∧ l.length=5 := by decide +kernel
  exact h l hl

def bits (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) (k : Fin 10) : Bool :=
  if k.val=0 then b0 else if k.val=1 then b1 else if k.val=2 then b2 else if k.val=3 then b3
  else if k.val=4 then b4 else if k.val=5 then b5 else if k.val=6 then b6 else if k.val=7 then b7
  else if k.val=8 then b8 else b9

def check (m : Bits) : Prop :=
  (∀ a, 1≤deg m a) →
  (∀ a b,a≠b → 2≤deg m a ∨ 2≤deg m b) →
  ∃ l∈paths, l.Chain' (fun u v => edge m u v=true)

noncomputable instance (m : Bits) : Decidable (check m) := by unfold check; infer_instance

def Row (b0 b1 b2 b3 : Bool) : Prop :=
  ∀ b4 b5 b6 b7 b8 b9, check (bits b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)

noncomputable instance (b0 b1 b2 b3 : Bool) : Decidable (Row b0 b1 b2 b3) := by unfold Row; infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem rows (b0 b1 b2 b3 : Bool) : Row b0 b1 b2 b3 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide +kernel

theorem tiny (m : Bits) : check m := by
  have eq : bits (m 0) (m 1) (m 2) (m 3) (m 4) (m 5) (m 6) (m 7) (m 8) (m 9)=m := by
    funext i
    fin_cases i <;> rfl
  simpa only [eq] using rows (m 0) (m 1) (m 2) (m 3) (m 4) (m 5) (m 6) (m 7) (m 8) (m 9)

#print axioms tiny
end GraffitiSmallCoreFive
