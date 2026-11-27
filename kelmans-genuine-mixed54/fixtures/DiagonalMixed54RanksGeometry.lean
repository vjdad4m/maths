import DiagonalMixed54Ranks

open Finset SimpleGraph
open scoped BigOperators
set_option maxHeartbeats 0
namespace KelmansCactus.AtomicBridge.DiagonalMixed54
open SquareCap (boundary HasFactor)

private theorem adjFalse (v : Core) : core.Adj v (mate false v) := by
  fin_cases v <;> decide
private theorem adjTrue (v : Core) : core.Adj v (mate true v) := by
  fin_cases v <;> decide
theorem mate_adjacent : ∀ k (v : Core),core.Adj v (mate k v) := by
  intro k
  cases k
  · exact adjFalse
  · exact adjTrue

theorem no_charges : ∀ k i,mate k (a i)≠b i := by decide

#print axioms mate_adjacent
#print axioms no_charges

def square : Finset Core := {1,2,7,8}
def spokes : Finset (Core×Core) := {(1,0),(2,3),(7,6),(8,9)}
def squareSides : Finset (Core×Core) := {(1,2),(2,8),(8,7),(7,1)}
open RemoteCutCertificate
private def insideSquare (e : Core×Core) : Prop :=
  e.1∈square ∧ e.2∈square
private def touchesSquare (e : Core×Core) : Prop :=
  (e.1∈square ∧ e.2∉square) ∨ (e.2∈square ∧ e.1∉square)
instance (e : Core×Core) : Decidable (insideSquare e) := by unfold insideSquare; infer_instance
instance (e : Core×Core) : Decidable (touchesSquare e) := by unfold touchesSquare; infer_instance

set_option maxRecDepth 16000 in
theorem genuine_release :
    (∀ i : RemoteSpacedPrismHandle.Port,a i∉square ∧ b i∉square) ∧
    (∀ x y : Core,x∈square → y∈square →
      (core.Adj x y ↔ (x,y)∈squareSides ∨ (y,x)∈squareSides)) ∧
    (∀ x y : Core,(x∈square ∧ y∉square ∧ core.Adj x y) ↔ (x,y)∈spokes) ∧
    (∀ e∈spokes,mate false e.1=e.2 ∧ mate true e.1≠e.2) := by
  constructor
  · decide
  constructor
  · intro x y hx hy
    have check : edgeTable.edges.all
        (fun e=>decide (insideSquare e → e∈squareSides ∨ e.swap∈squareSides)) = true := by decide
    have tab (e : Core×Core) (inList : e∈edgeTable.edges) :
        insideSquare e → e∈squareSides ∨ e.swap∈squareSides :=
      of_decide_eq_true (List.all_eq_true.mp check e inList)
    have yes : ∀ e∈squareSides,core.Adj e.1 e.2 := by decide
    constructor
    · rintro (edge|edge)
      · exact tab (x,y) edge ⟨hx,hy⟩
      · exact (tab (y,x) edge ⟨hy,hx⟩).symm
    · intro h
      exact h.elim (fun e=>yes (x,y) e) (fun e=>(yes (y,x) e).symm)
  constructor
  · intro x y
    have check : edgeTable.edges.all
        (fun e=>decide (touchesSquare e → e∈spokes ∨ e.swap∈spokes)) = true := by decide
    have tab (e : Core×Core) (inList : e∈edgeTable.edges) :
        touchesSquare e → e∈spokes ∨ e.swap∈spokes :=
      of_decide_eq_true (List.all_eq_true.mp check e inList)
    have yes : ∀ e∈spokes,e.1∈square ∧ e.2∉square ∧ core.Adj e.1 e.2 := by decide
    constructor
    · rintro ⟨hx,hy,h⟩
      have sym : (y,x)∈spokes → False := fun e=>(yes (y,x) e).2.1 hx
      rcases h with edge|edge
      · exact (tab (x,y) edge (Or.inl ⟨hx,hy⟩)).resolve_right sym
      · exact (tab (y,x) edge (Or.inr ⟨hx,hy⟩)).resolve_left sym
    · exact yes (x,y)
  · decide

#print axioms genuine_release

private def activeList : List (Core×Core) := [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),(10,11),(11,12),(12,13),(13,14),(14,15),(15,16),(16,17),(17,18),(18,19),(19,20),(20,21),(21,22),(22,23),(23,24),(24,25),(25,26),(26,27),(27,28),(28,29),(29,30),(30,31),(31,32),(32,33),(33,34),(34,35),(35,0)]

def active : Finset (Core×Core) := activeList.toFinset

set_option maxRecDepth 14000 in
theorem exchange_exact (x y : Core) :
    ((mate false x=y ∧ mate true x≠y) ∨ (mate true x=y ∧ mate false x≠y)) ↔
      (x,y)∈active ∨ (y,x)∈active := by
  have fromMate : ∀ t : Core,
      (mate false t≠mate true t →
        (((t,mate false t)∈active ∨ (mate false t,t)∈active) ∧
        ((t,mate true t)∈active ∨ (mate true t,t)∈active))) := by
    intro t
    have small : mate false t≠mate true t →
        (((t,mate false t)∈activeList ∨ (mate false t,t)∈activeList) ∧
         ((t,mate true t)∈activeList ∨ (mate true t,t)∈activeList)) := by
      fin_cases t <;> decide
    simpa only [active,List.mem_toFinset] using small
  have fromEdge : ∀ e∈active,
      ((mate false e.1=e.2 ∧ mate true e.1≠e.2) ∨
        (mate true e.1=e.2 ∧ mate false e.1≠e.2)) ∧
      ((mate false e.2=e.1 ∧ mate true e.2≠e.1) ∨
        (mate true e.2=e.1 ∧ mate false e.2≠e.1)) := by
    have check : activeList.all (fun e=>decide
        (((mate false e.1=e.2 ∧ mate true e.1≠e.2) ∨
          (mate true e.1=e.2 ∧ mate false e.1≠e.2)) ∧
         ((mate false e.2=e.1 ∧ mate true e.2≠e.1) ∨
          (mate true e.2=e.1 ∧ mate false e.2≠e.1)))) = true := by decide
    intro e he
    exact of_decide_eq_true (List.all_eq_true.mp check e (List.mem_toFinset.mp he))
  constructor
  · rintro (⟨h,k⟩|⟨h,k⟩)
    · have n : mate false x≠mate true x := fun e=>k (e.symm.trans h)
      exact h ▸ (fromMate x n).1
    · have n : mate false x≠mate true x := fun e=>k (e.trans h)
      exact h ▸ (fromMate x n).2
  · rintro (h|h)
    · exact (fromEdge (x,y) h).1
    · exact (fromEdge (y,x) h).2

#print axioms exchange_exact
end KelmansCactus.AtomicBridge.DiagonalMixed54
