import Threshold
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace BadScienceSeven
theorem verified0 (a : Fin 1) : checkPrefix 0 a.val = true := by
  rw [show a.val = 0 by omega]; decide +kernel
#print axioms verified0
end BadScienceSeven
