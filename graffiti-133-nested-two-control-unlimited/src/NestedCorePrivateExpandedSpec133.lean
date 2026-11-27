import NestedCorePrivateGenericKernel133

namespace Graffiti133ExpandedPrivate
open SimpleGraph Graffiti133 Graffiti133PrivateGeneric
open scoped Classical
set_option maxHeartbeats 1000000

def baseFragment (m : Bool) (x y : Nat) (hy : y < 18) (xy : x≤y) : Option Bool :=
  if x < 9 then some (Graffiti133PrivateCross.base m ⟨x,lt_of_le_of_lt xy hy⟩ ⟨y,hy⟩) else none

def singleCase (m : Bool) (c : Fin 2) (i : Fin 7) (wide opp : Bool) (a b : Fin 19) : Option Bool :=
  let x := min a.val b.val
  let y := max a.val b.val
  if hy : y < 18 then baseFragment m x y hy (min_le_max ..)
  else if x < 9 then
    some (decide (x=i.val ∨ (wide=true ∧ x=(i+1).val) ∨ (opp=true ∧ x=8-c.val)))
  else if x=c.val+16 then some true else none

def dualSingleCase (m : Bool) (i : Fin 7) (a b : Fin 19) : Option Bool :=
  let x := min a.val b.val
  let y := max a.val b.val
  if hy : y < 18 then baseFragment m x y hy (min_le_max ..)
  else if x < 9 then some (decide (x=7 ∨ x=8))
  else if x=i.val+9 then some true else none

def dualAdjacentCase (m : Bool) (i : Fin 7) (a b : Fin 20) : Option Bool :=
  let x := min a.val b.val
  let y := max a.val b.val
  if hy : y < 18 then baseFragment m x y hy (min_le_max ..)
  else if y=18 then
    if x < 9 then some (decide (x=7 ∨ x=8)) else none
  else if x < 9 then some (decide (x=i.val ∨ x=(i+1).val))
  else if x=18 then some true else none

end Graffiti133ExpandedPrivate
