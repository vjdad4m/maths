import Std
import Lean

namespace BadScienceSeven

def sgn (i : Nat) : Int := if i % 2 = 0 then 1 else -1

-- A three-coordinate row for the two-bit value zero; six four-coordinate rows
-- for the other three two-bit values, subdivided by the third bit.
def numerator (r j : Nat) : Int :=
  match j with
  | 0 => 1
  | 1 => if r = 0 then 1 else sgn ((r+1)/2)
  | 2 => if r = 0 then 1 else sgn ((r+1)/4)
  | 3 => if r = 0 then 0 else sgn (r+1)
  | _ => 0

def count (r : Nat) : Nat := if r = 0 then 3 else 4

def selected (i : Nat) : Nat := if i % 4 = 0 then 0 else (i%4)*2 - 1 + (i/4)%2

def x (i j : Nat) : Int := if j=0 then 1 else sgn (i/2^(j-1))
def dot (r i : Nat) : Int := ((List.range 7).map (fun j => numerator r j * x i j)).sum
def sqnorm (r : Nat) : Int := ((List.range 7).map (fun j => numerator r j ^ 2)).sum

theorem rows : ∀ r : Fin 7, sqnorm r.val = (count r.val : Int) := by
  decide +kernel

theorem chosen : ∀ i : Fin 64, selected i.val < 7 ∧
    dot (selected i.val) i.val = (count (selected i.val) : Int) := by
  decide +kernel

theorem cell_counts :
    ((List.range 64).filter (fun i => selected i = 0)).length = 16 ∧
    ((List.range 64).filter (fun i => selected i ≠ 0)).length = 48 := by
  decide +kernel

#print axioms rows
#print axioms chosen
#print axioms cell_counts

end BadScienceSeven
