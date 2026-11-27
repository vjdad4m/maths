import TinyFourOrder13Model189

namespace FourOrder13
open Finset
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem tbl6 : Table 6 (by decide) := by
  intro a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;> unfold TableShard <;> decide +kernel

#print axioms tbl6
end FourOrder13
