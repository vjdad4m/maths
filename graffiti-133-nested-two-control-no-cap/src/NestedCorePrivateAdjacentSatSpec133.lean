import NestedCorePrivateExpandedSpec133
import NestedCorePrivateActiveKernel133

namespace Graffiti133NestedWeightedCore
open SimpleGraph Graffiti133 Graffiti133PrivateGeneric Graffiti133PrivateCross Graffiti133ExpandedPrivate Graffiti133NestedActive
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

def satSite (i : Fin 7) (d : Fin 3) : Fin 7 := ⟨(i.val+3+d.val)%7,Nat.mod_lt _ (by decide)⟩
def satAlias (mask : Fin 8) (d : Fin 3) : Bool := mask.val.testBit d.val

def satActive (mask : Fin 8) (a : Fin 22) : Bool := decide (a.val<19) || !(mask.val.testBit (a.val-19))

def satSpec (m : Bool) (i : Fin 7) (mask : Fin 8) (a b : Fin 22) : Option Bool :=
  let x := min a.val b.val
  let y := max a.val b.val
  if hy : y<18 then baseFragment m x y hy (min_le_max ..)
  else if y=18 then
    if x<7 then some (decide (x=i.val ∨ x=(i+1).val))
    else if ∃ d : Fin 3,satAlias mask d=true ∧ x=9+(satSite i d).val then some true else none
  else
    if h : y-19<3 then
      let d : Fin 3 := ⟨y-19,h⟩
      if satAlias mask d then none
      else if x<7 then some (decide (x=(satSite i d).val))
      else if x=18 then some true else none
    else none

end Graffiti133NestedWeightedCore
