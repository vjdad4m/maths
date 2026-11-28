import Threshold
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace BadScienceSeven
theorem verified3 (a : Fin 2) : checkPrefix 3 a.val = true := by
  have h : ↑a = 0 ∨ ↑a = 1 := by omega
  rcases h with h|h <;> rw [h] <;> decide +kernel
#print axioms verified3
end BadScienceSeven
