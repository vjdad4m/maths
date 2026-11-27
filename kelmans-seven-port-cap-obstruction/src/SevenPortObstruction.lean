import ThetaExteriorFixture
import Mathlib.Tactic.FinCases

open Finset
namespace KelmansCactus.AtomicBridge.SevenPortObstruction
open ThetaExteriorFixture (es X graph)

abbrev Ear := Fin 8
abbrev Layout := Fin 3
abbrev Point := Fin 19

private def data : Array (Point × Point × List Point) := #[(7,12,[8,9,10,11,14,8,10]),(7,14,[8,9,10,11,12,15,11]),(9,13,[11,7,10,8,15,10,11]),(9,15,[11,7,10,8,13,14,8]),(11,13,[9,8,10,7,14,9,10]),(11,14,[9,8,10,7,13,15,7]),(8,12,[7,11,10,9,15,7,10]),(8,15,[7,11,10,9,12,14,9])]

def x (i : Ear) : Point := (data[i.val]?.getD (0,0,[])).1
def y (i : Ear) : Point := (data[i.val]?.getD (0,0,[])).2.1
def contacts (i : Ear) : List Point := (data[i.val]?.getD (0,0,[])).2.2

abbrev live (a : X) : Prop := a=7 ∨ a=8 ∨ a=9 ∨ a=11

theorem exhausts_live_ears :
    ∀ a b : X,live a → 7 ≤ b.val → graph.Adj a b →
      ∃ i : Ear,(x i).val=a.val ∧ (y i).val=b.val := by
  decide

def assign (l : Layout) (p : Nat) : Point :=
  if p=5 ∨ p=6 then 18
  else if (l=0 ∧ (p=0 ∨ p=3)) ∨ (l=1 ∧ (p=0 ∨ p=4)) ∨
      (l=2 ∧ (p=3 ∨ p=4)) then 17
  else 16

def lift (a : X) : Point := ⟨a.val,by have lb:=a.isLt; omega⟩
def active (i : Ear) (v : Point) : Bool := decide (7 ≤ v.val ∧ v≠x i ∧ v≠y i)

def capEdges (i : Ear) (l : Layout) : List (Point×Point) :=
  ((es.map (fun (a,b)=>(lift a,lift b))).filter (fun (a,b)=>active i a && active i b)) ++
  [(17,18)] ++ ((contacts i).zipIdx.map (fun (v,p)=>(v,assign l p)))

private def shores : Array (Array (List Point)) := #[#[[9,10,11,13,14,15,16],[9,10,11,13,16],[11,14,17]],#[[10,12,16],[9,10,11,13,16],[8,9,10,12,13,15,16]],#[[7,8,10,12,14,15,16],[7,8,10,12,16],[8,15,17]],#[[10,13,16],[7,8,10,12,16],[7,10,11,12,13,14,16]],#[[7,8,10,12,14,15,16],[7,8,10,12,16],[7,14,17]],#[[10,13,16],[7,8,10,12,16],[8,9,10,12,13,15,16]],#[[9,10,11,13,14,15,16],[9,10,11,13,16],[9,15,17]],#[[10,12,16],[9,10,11,13,16],[7,10,11,12,13,14,16]]]
def shore (i : Ear) (l : Layout) : List Point :=
  ((shores[i.val]?.getD #[])[l.val]?.getD [])

def other (i : Ear) (l : Layout) : Finset Point :=
  ((univ : Finset Point).filter (fun v=>active i v)) \ (shore i l).toFinset

private def Checked (i : Ear) (l : Layout) : Prop :=
  (∀ v∈(shore i l).toFinset,active i v=true) ∧
  2 ≤ (shore i l).toFinset.card ∧ 2 ≤ (other i l).card ∧
  (capEdges i l).Nodup ∧
  (∀ z∈(capEdges i l).toFinset,active i z.1=true ∧ active i z.2=true ∧ z.1<z.2) ∧
  (capEdges i l).countP (fun (a,b)=>((shore i l).contains a) != ((shore i l).contains b))=3

private instance (i : Ear) (l : Layout) : Decidable (Checked i l) := by
  unfold Checked
  infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem checked_all (i : Ear) (l : Layout) : Checked i l := by
  fin_cases i <;> fin_cases l <;> decide

/-- Explicit nontrivial three-edge shore for each of the 24 concrete
edge-plus-singleton caps. The edge listing consists of the actual
induced exterior, the cap's one internal edge, and its seven wires. -/
theorem all_twenty_four_bad (i : Ear) (l : Layout) :
    (∀ v∈(shore i l).toFinset,active i v=true) ∧
    2 ≤ (shore i l).toFinset.card ∧ 2 ≤ (other i l).card ∧
    (capEdges i l).Nodup ∧
    (∀ z∈(capEdges i l).toFinset,active i z.1=true ∧ active i z.2=true ∧ z.1<z.2) ∧
    (capEdges i l).countP (fun (a,b)=>((shore i l).contains a) != ((shore i l).contains b))=3 :=
  checked_all i l

#print axioms exhausts_live_ears
#print axioms all_twenty_four_bad
end KelmansCactus.AtomicBridge.SevenPortObstruction
