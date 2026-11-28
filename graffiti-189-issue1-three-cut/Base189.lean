import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Powerset

/- Concrete derivative of duggiephresh's G?qtfo clique blow-up; see README. -/
namespace Issue189
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
abbrev V := Fin 34
abbrev I := Fin 8
def bag (v : V) : I :=
  if v.val < 3 then 0 else if v.val < 6 then 1 else if v.val < 9 then 2
  else if v.val < 15 then 3 else if v.val < 21 then 4 else if v.val < 22 then 5
  else if v.val < 23 then 6 else 7
def len (i j : I) : Nat := (#[0, 2, 1, 2, 2, 1, 1, 1, 2, 0, 1, 2, 2, 3, 3, 1, 1, 1, 0, 2, 2, 2, 2, 1, 2, 2, 2, 0, 2, 1, 1, 1, 2, 2, 2, 2, 0, 1, 1, 1, 1, 3, 2, 1, 1, 0, 2, 2, 1, 3, 2, 1, 1, 2, 0, 2, 1, 1, 1, 1, 1, 2, 2, 0] : Array Nat)[8*i.val+j.val]!
def step (i j : I) : V := (#[0, 6, 6, 21, 21, 21, 22, 23, 6, 3, 6, 23, 23, 6, 6, 23, 0, 3, 6, 23, 23, 0, 0, 23, 21, 23, 23, 9, 21, 21, 22, 23, 21, 23, 23, 21, 15, 21, 22, 23, 0, 0, 0, 9, 15, 21, 0, 0, 0, 0, 0, 9, 15, 0, 22, 0, 0, 3, 6, 9, 15, 0, 0, 23] : Array V)[8*i.val+j.val]!
def touch (i j : I) := len i j = 1
instance : DecidableRel touch := fun _ _ => inferInstanceAs (Decidable (_ = 1))
theorem tsym : ∀ (i j : I), touch i j → touch j i := by decide
def adj (u v : V) := u ≠ v ∧ (bag u = bag v ∨ touch (bag u) (bag v))
instance : DecidableRel adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
def G : SimpleGraph V where
  Adj := adj
  symm _ _ h := ⟨h.1.symm,h.2.elim (fun h => Or.inl h.symm) (fun h => Or.inr (tsym _ _ h))⟩
  loopless _ h := h.1 rfl
instance : DecidableRel G.Adj := inferInstanceAs (DecidableRel adj)
end Issue189
