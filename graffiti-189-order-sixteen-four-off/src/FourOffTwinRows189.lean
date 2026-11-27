import FourOffTwinModel189

namespace OffFour16Twin

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private theorem row_4 : row 4=true := by decide +kernel
#print axioms row_4

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private theorem row_5 : row 5=true := by decide +kernel
#print axioms row_5

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private theorem row_6 : row 6=true := by decide +kernel
#print axioms row_6

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private theorem row_7 : row 7=true := by decide +kernel
#print axioms row_7

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private theorem row_8 : row 8=true := by decide +kernel
#print axioms row_8

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
private theorem row_9 : row 9=true := by decide +kernel
#print axioms row_9

theorem all_rows (j : ℕ) (lo : 4≤j) (hi : j≤9) : row j=true := by
  have h : j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
  rcases h with e|e|e|e|e|e
  · exact Eq.mpr (congrArg (fun j' => row j'=true) e) row_4
  · exact Eq.mpr (congrArg (fun j' => row j'=true) e) row_5
  · exact Eq.mpr (congrArg (fun j' => row j'=true) e) row_6
  · exact Eq.mpr (congrArg (fun j' => row j'=true) e) row_7
  · exact Eq.mpr (congrArg (fun j' => row j'=true) e) row_8
  · exact Eq.mpr (congrArg (fun j' => row j'=true) e) row_9
#print axioms all_rows

end OffFour16Twin
