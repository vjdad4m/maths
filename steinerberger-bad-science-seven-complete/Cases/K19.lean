import Threshold
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace BadScienceSeven
theorem verified19 (a : Fin 10) : checkPrefix 19 a.val = true := by
  have h : ↑a = 0 ∨ ↑a = 1 ∨ ↑a = 2 ∨ ↑a = 3 ∨ ↑a = 4 ∨ ↑a = 5 ∨ ↑a = 6 ∨ ↑a = 7 ∨ ↑a = 8 ∨ ↑a = 9 := by omega
  rcases h with h|h|h|h|h|h|h|h|h|h <;> rw [h] <;> decide +kernel
#print axioms verified19
end BadScienceSeven
