import Threshold
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace BadScienceSeven
theorem verified6 (a : Fin 4) : checkPrefix 6 a.val = true := by
  have h : ↑a = 0 ∨ ↑a = 1 ∨ ↑a = 2 ∨ ↑a = 3 := by omega
  rcases h with h|h|h|h <;> rw [h] <;> decide +kernel
#print axioms verified6
end BadScienceSeven
