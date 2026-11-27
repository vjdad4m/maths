import ThetaSevenFaithfulLocalCut
import Mathlib.Tactic.FinCases

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaAsymmetricFaithfulTable
open ThetaSevenFaithfulCap (edges3 edges9)
open ThetaSevenFaithfulLocalCut (fromBits)

abbrev Wire := Fin 7

def oldWires : List (Wire×Fin 9) :=
  [(0,2),(1,4),(2,6),(3,5),(4,7),(5,8),(6,8)]

/-- A gets p2,p3; B gets p1,p4; C keeps its two true wires
and uses t, not p2, as the omitted auxiliary wire. -/
def newWires : List (Wire×Fin 3) :=
  [(0,1),(1,0),(2,0),(3,1),(4,2),(5,2),(6,2)]

def formerWires : List (Wire×Fin 3) :=
  [(0,1),(1,2),(2,0),(3,1),(4,0),(5,2),(6,2)]

def cost {I : Type*} (e : List (I×I)) (w : List (Wire×I))
    (c : Wire→Bool) (s : I→Bool) : ℕ :=
  e.countP (fun v=>s v.1 != s v.2) + w.countP (fun v=>c v.1 != s v.2)

private def witness : Array ℕ := #[0,0,0,0,0,0,0,127,0,0,0,127,0,127,121,127,0,0,0,0,0,0,0,255,0,0,0,255,0,255,255,255,0,0,0,0,0,0,0,127,0,0,0,127,0,127,121,127,0,0,0,511,0,463,511,511,0,511,511,511,511,511,511,511,0,0,0,0,0,0,0,127,0,0,0,127,0,127,121,127,0,0,0,511,0,463,511,511,0,511,511,511,511,511,511,511,256,256,256,256,256,256,256,511,256,256,256,511,256,511,511,511,384,384,384,511,384,463,511,511,384,511,511,511,511,511,511,511]

set_option maxRecDepth 3000 in
private theorem bounded (p : Fin 128) (v : Fin 8) :
    cost edges9 oldWires (fromBits p.val) (fromBits (witness[p.val]?.getD 0)) ≤
      cost edges3 newWires (fromBits p.val) (fromBits v.val)+1 := by
  have check : ∀ v : Fin 8,∀ p : Fin 128,
    cost edges9 oldWires (fromBits p.val) (fromBits (witness[p.val]?.getD 0)) ≤
      cost edges3 newWires (fromBits p.val) (fromBits v.val)+1 := by
    intro x
    fin_cases x <;> decide
  exact check v p

private def boolNum (b : Bool) : ℕ := if b then 1 else 0

private def code7 (a b c d e f g : Bool) : Fin 128 :=
  ⟨boolNum a+2*boolNum b+4*boolNum c+8*boolNum d+16*boolNum e+32*boolNum f+64*boolNum g,
      by unfold boolNum; split <;> split <;> split <;> split <;> split <;> split <;> split <;> omega⟩

private def code3 (a b c : Bool) : Fin 8 :=
  ⟨boolNum a+2*boolNum b+4*boolNum c,
      by unfold boolNum; split <;> split <;> split <;> omega⟩

private theorem recover7 : ∀ a b c d e f g : Bool,∀ i : Wire,
    fromBits (code7 a b c d e f g).val i =
      (if i=0 then a else if i=1 then b else if i=2 then c else if i=3 then d
        else if i=4 then e else if i=5 then f else g) := by decide
private theorem recover3 : ∀ a b c : Bool,∀ i : Fin 3,
    fromBits (code3 a b c).val i = (if i=0 then a else if i=1 then b else c) := by decide

/-- This local comparison does not require the seven wire labels to
have distinct exterior endpoints. Repeated contacts simply have the
same color at their two wire labels. -/
theorem local_cut_domination (c : Wire→Bool) (s : Fin 3→Bool) :
    ∃ t : Fin 9→Bool,cost edges9 oldWires c t ≤ cost edges3 newWires c s+1 := by
  let p := code7 (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6)
  let v := code3 (s 0) (s 1) (s 2)
  have a : fromBits p.val=c := by
    funext i
    simp only [p,recover7]
    fin_cases i <;> rfl
  have b : fromBits v.val=s := by
    funext i
    simp only [v,recover3]
    fin_cases i <;> rfl
  exact ⟨_,by simpa only [a,b] using bounded p v⟩

#print axioms local_cut_domination
end KelmansCactus.AtomicBridge.ThetaAsymmetricFaithfulTable
