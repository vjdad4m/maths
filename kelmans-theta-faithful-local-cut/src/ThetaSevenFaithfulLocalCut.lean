import ThetaSevenFaithfulCap
import Mathlib.Tactic.FinCases

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaSevenFaithfulLocalCut
open PentagonProfile (Port)
open ThetaSevenFaithfulCap (edges9 edges3 wire9 wire3)

def oldWires : List (Port×Fin 9) := [(0,2),(0,8),(1,4),(2,6),(2,8),(3,5),(4,7)]
def capWires : List (Port×Fin 3) := [(0,1),(0,2),(1,2),(2,0),(2,2),(3,1),(4,0)]

theorem exact_old_wires : ∀ p : Port,∀ x : Fin 9,wire9 p x=true ↔ (p,x)∈oldWires := by decide
theorem exact_cap_wires : ∀ p : Port,∀ x : Fin 3,wire3 p x=true ↔ (p,x)∈capWires := by decide

def cost {I : Type*} (edges : List (I×I)) (wires : List (Port×I))
    (c : Port→Bool) (s : I→Bool) : ℕ :=
  edges.countP (fun e=>s e.1 != s e.2) +
  wires.countP (fun w=>c w.1 != s w.2)

private def witness : Array ℕ := #[0,0,0,0,0,256,0,511,0,0,0,127,0,511,121,511,0,0,0,511,0,463,511,511,0,511,0,511,511,511,511,511]

def fromBits {k : ℕ} (mask : ℕ) (i : Fin k) : Bool := Nat.testBit mask i.val

private theorem bounded (p : Fin 32) (v : Fin 8) :
    cost edges9 oldWires (fromBits p.val) (fromBits (witness[p.val]?.getD 0)) ≤
      cost edges3 capWires (fromBits p.val) (fromBits v.val)+1 := by
  have check : ∀ p : Fin 32,∀ v : Fin 8,
    cost edges9 oldWires (fromBits p.val) (fromBits (witness[p.val]?.getD 0)) ≤
      cost edges3 capWires (fromBits p.val) (fromBits v.val)+1 := by decide
  exact check p v

private def boolNum (b : Bool) : ℕ := if b then 1 else 0

private def code5 (a b c d e : Bool) : Fin 32 :=
  ⟨boolNum a+2*boolNum b+4*boolNum c+8*boolNum d+16*boolNum e,
      by unfold boolNum; split <;> split <;> split <;> split <;> split <;> omega⟩

private def code3 (a b c : Bool) : Fin 8 :=
  ⟨boolNum a+2*boolNum b+4*boolNum c,
      by unfold boolNum; split <;> split <;> split <;> omega⟩

private theorem recover5 : ∀ a b c d e : Bool,∀ i : Port,
    fromBits (code5 a b c d e).val i =
      (if i=0 then a else if i=1 then b else if i=2 then c else if i=3 then d else e) := by decide
private theorem recover3 : ∀ a b c : Bool,∀ i : Fin 3,
    fromBits (code3 a b c).val i = (if i=0 then a else if i=1 then b else c) := by decide

theorem local_cut_domination (c : Port→Bool) (s : Fin 3→Bool) :
    ∃ t : Fin 9→Bool,cost edges9 oldWires c t ≤ cost edges3 capWires c s+1 := by
  let p := code5 (c 0) (c 1) (c 2) (c 3) (c 4)
  let v := code3 (s 0) (s 1) (s 2)
  have a : fromBits p.val=c := by
    funext i
    simp only [p,recover5]
    fin_cases i <;> rfl
  have b : fromBits v.val=s := by
    funext i
    simp only [v,recover3]
    fin_cases i <;> rfl
  exact ⟨_,by simpa only [a,b] using bounded p v⟩

#print axioms local_cut_domination
end KelmansCactus.AtomicBridge.ThetaSevenFaithfulLocalCut
