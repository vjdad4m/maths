import TinyFourOrder14OneTable

namespace FourOrder14One
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem tbl111_part0 : ∀ b c d : Fin 3, Shard 1 11 (by decide) (by decide) 0 b c d := by
  intro b c d
  fin_cases b <;> fin_cases c <;> fin_cases d <;> unfold Shard <;> decide +kernel

#print axioms tbl111_part0
end FourOrder14One
