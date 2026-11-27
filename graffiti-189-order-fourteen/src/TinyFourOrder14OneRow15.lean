import TinyFourOrder14OneTable

namespace FourOrder14One
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem tbl15 : Table 1 5 (by decide) (by decide) := by
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> unfold Shard <;> decide +kernel

#print axioms tbl15
end FourOrder14One
