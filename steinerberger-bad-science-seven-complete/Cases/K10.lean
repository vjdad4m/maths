import Threshold
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace BadScienceSeven
theorem verified10 (a : Fin 6) : checkPrefix 10 a.val = true := by
  have h : ↑a = 0 ∨ ↑a = 1 ∨ ↑a = 2 ∨ ↑a = 3 ∨ ↑a = 4 ∨ ↑a = 5 := by omega
  rcases h with h|h|h|h|h|h <;> rw [h] <;> decide +kernel
#print axioms verified10
end BadScienceSeven
