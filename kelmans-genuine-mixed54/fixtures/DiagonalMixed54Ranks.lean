import DiagonalMixed54Core

open Finset SimpleGraph
open scoped BigOperators
set_option maxHeartbeats 0
namespace KelmansCactus.AtomicBridge.DiagonalMixed54
open SquareCap (boundary HasFactor)

def mate (k : Bool) (v : Core) : Core :=
  (if k then [35,2,1,4,3,6,5,8,7,10,9,12,11,14,13,16,15,18,17,20,19,22,21,24,23,26,25,28,27,30,29,32,31,34,33,0,43,45,41,44,47,38,46,36,39,37,42,40] else [1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14,17,16,19,18,21,20,23,22,25,24,27,26,29,28,31,30,33,32,35,34,43,45,41,44,47,38,46,36,39,37,42,40] : List Core)[v.val]!
theorem mate_involutive (k : Bool) : Function.Involutive (mate k) := by
  cases k
  · have ok : (List.finRange 48).all (fun v=>decide (mate false (mate false v)=v))=true := by decide
    intro v
    exact of_decide_eq_true (List.all_eq_true.mp ok v (by simp))
  · have ok : (List.finRange 48).all (fun v=>decide (mate true (mate true v)=v))=true := by decide
    intro v
    exact of_decide_eq_true (List.all_eq_true.mp ok v (by simp))

def rank (k : Bool) : SimpleGraph Board where
  Adj x y := board.Adj x y ∧ match x,y with
    | .inl u,.inl v => mate k u≠v
    | _,_ => True
  symm := by
    rintro (x|i) (y|j) h
    · exact ⟨h.1.symm,fun e=>h.2 (by rw [←e,mate_involutive])⟩
    all_goals exact ⟨h.1.symm,trivial⟩
  loopless x h := board.loopless x h.1

instance (k : Bool) : DecidableRel (rank k).Adj := by
  rintro (x|i) (y|j)
  all_goals change Decidable (_ ∧ _)
  all_goals infer_instance

def pairUnion : SimpleGraph Board := rank false ⊔ rank true
instance : DecidableRel pairUnion.Adj := by
  intro x y
  change Decidable ((rank false).Adj x y ∨ (rank true).Adj x y)
  infer_instance

theorem pair_le : pairUnion ≤ board := by
  intro x y h
  change (rank false).Adj x y ∨ (rank true).Adj x y at h
  exact h.elim (·.1) (·.1)



#print axioms mate_involutive
end KelmansCactus.AtomicBridge.DiagonalMixed54
