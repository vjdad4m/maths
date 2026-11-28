import Std
import Lean

namespace BadScienceEight

def signBit (i : Nat) : Int := if i % 2 = 0 then 1 else -1

def numerator (r j : Nat) : Int :=
  if j = 0 then 1 else if j ≤ 3 then signBit (r/2^(j-1)) else 0

def selected (i : Nat) : Nat := i%8

def x (i j : Nat) : Int := if j=0 then 1 else signBit (i/2^(j-1))
def dot (r i : Nat) : Int := ((List.range 8).map (fun j => numerator r j * x i j)).sum
def sqnorm (r : Nat) : Int := ((List.range 8).map (fun j => numerator r j ^ 2)).sum

theorem rows : ∀ r : Fin 8, sqnorm r.val = 4 := by decide +kernel

theorem chosen : ∀ i : Fin 128, selected i.val < 8 ∧ dot (selected i.val) i.val = 4 := by
  decide +kernel

#print axioms rows
#print axioms chosen
end BadScienceEight
