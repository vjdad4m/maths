import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Chain
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

namespace Graffiti189EightTerminal

/-- A minimal completed eight-point wing: three universal nonports plus
one original port-port edge. Port colors are the first two and next three. -/
def allowed (i j u v : Fin 8) : Prop :=
  u ≠ v ∧ (5 ≤ u.val ∨ 5 ≤ v.val ∨ (u = i ∧ v = j) ∨ (u = j ∧ v = i))

instance (i j u v : Fin 8) : Decidable (allowed i j u v) := by
  unfold allowed
  infer_instance

def completedRoute (i j : Fin 8) : Prop :=
  ∃ L : List (Fin 8), L.Nodup ∧ (∀ k : Fin 8, k ∈ L) ∧
    L.Chain' (allowed i j) ∧
    (∃ k ∈ ([0,1] : List (Fin 8)), L.head? = some k) ∧
    (∃ k ∈ ([2,3,4] : List (Fin 8)), L.getLast? = some k)

theorem completed_route (i j : Fin 8) (hi : i.val < 5) (hj : j.val < 5)
    (ne : i ≠ j) : completedRoute i j := by
  fin_cases i <;> fin_cases j <;> try contradiction
  · exact ⟨[0,1,5,2,6,3,7,4], by decide +kernel⟩
  · exact ⟨[0,2,5,1,6,3,7,4], by decide +kernel⟩
  · exact ⟨[0,3,5,1,6,2,7,4], by decide +kernel⟩
  · exact ⟨[0,4,5,1,6,2,7,3], by decide +kernel⟩
  · exact ⟨[0,1,5,2,6,3,7,4], by decide +kernel⟩
  · exact ⟨[0,5,1,2,6,3,7,4], by decide +kernel⟩
  · exact ⟨[0,5,1,3,6,2,7,4], by decide +kernel⟩
  · exact ⟨[0,5,1,4,6,2,7,3], by decide +kernel⟩
  · exact ⟨[0,2,5,1,6,3,7,4], by decide +kernel⟩
  · exact ⟨[0,5,1,2,6,3,7,4], by decide +kernel⟩
  · exact ⟨[0,5,1,6,2,3,7,4], by decide +kernel⟩
  · exact ⟨[0,5,1,6,2,4,7,3], by decide +kernel⟩
  · exact ⟨[0,3,5,1,6,2,7,4], by decide +kernel⟩
  · exact ⟨[0,5,1,3,6,2,7,4], by decide +kernel⟩
  · exact ⟨[0,5,1,6,2,3,7,4], by decide +kernel⟩
  · exact ⟨[0,5,1,6,2,7,3,4], by decide +kernel⟩
  · exact ⟨[0,4,5,1,6,2,7,3], by decide +kernel⟩
  · exact ⟨[0,5,1,4,6,2,7,3], by decide +kernel⟩
  · exact ⟨[0,5,1,6,2,4,7,3], by decide +kernel⟩
  · exact ⟨[0,5,1,6,2,7,3,4], by decide +kernel⟩

#print axioms completed_route
end Graffiti189EightTerminal
