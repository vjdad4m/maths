import Threshold
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace BadScienceSeven
theorem verified1 (a : Fin 1) : checkPrefix 1 a.val = true := by
  rw [show a.val = 0 by omega]; decide +kernel
#print axioms verified1
end BadScienceSeven
