import Threshold
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace BadScienceSeven
theorem verified5 (a : Fin 3) : checkPrefix 5 a.val = true := by
  have h : ↑a = 0 ∨ ↑a = 1 ∨ ↑a = 2 := by omega
  rcases h with h|h|h <;> rw [h] <;> decide +kernel
#print axioms verified5
end BadScienceSeven
