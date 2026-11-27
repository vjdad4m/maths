import NestedCorePrivateActiveKernel133
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Graffiti133NestedOneControl

open SimpleGraph Graffiti133 Graffiti133PrivateGeneric Graffiti133NestedActive
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def coreEdge (i j : Nat) : Bool :=
  if j<7 then decide ((i+1)%7=j ∨ (j+1)%7=i)
  else if j=7 then decide (i=0 ∨ i=3)
  else decide (j=i+8)

def trimSpec (i : Fin 7) (wide : Bool) (a b : Fin (if wide then 17 else 16)) : Option Bool :=
  let x := min a.val b.val
  let y := max a.val b.val
  if y<16 then
    if x<8 then some (coreEdge x y) else none
  else if y=16 then
    if x<8 then some (decide (x=i.val ∨ x=(i+1).val))
    else if x=15 then some true else none
  else none

def forcedTrimSpec (i : Fin 7) (wide : Bool) (a b : Fin (if wide then 17 else 16)) : Option Bool :=
  if wide then trimSpec i wide a b
  else if min a.val b.val=i.val+8 ∧ max a.val b.val=15 then some true else trimSpec i wide a b

def satSite (i : Fin 7) (d : Fin 3) : Fin 7 := ⟨(i.val+3+d.val)%7,Nat.mod_lt _ (by decide)⟩
def satAlias (mask : Fin 8) (d : Fin 3) : Bool := mask.val.testBit d.val
def satActive (mask : Fin 8) (a : Fin 20) : Bool := decide (a.val<17) || !(mask.val.testBit (a.val-17))

def satSpec (i : Fin 7) (mask : Fin 8) (a b : Fin 20) : Option Bool :=
  let x := min a.val b.val
  let y := max a.val b.val
  if y<16 then
    if x<8 then some (coreEdge x y) else none
  else if y=16 then
    if x<7 then some (decide (x=i.val ∨ x=(i+1).val))
    else if ∃ d : Fin 3,satAlias mask d=true ∧ x=8+(satSite i d).val then some true else none
  else
    if h : y-17<3 then
      let d : Fin 3 := ⟨y-17,h⟩
      if satAlias mask d then none
      else if x<7 then some (decide (x=(satSite i d).val))
      else if x=16 then some true else none
    else none

end Graffiti133NestedOneControl
