import OffFour15ReorderedBase
namespace OffFour15

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem row_4_8 : row 4 8=true := by decide +kernel
#print axioms row_4_8

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem row_4_9 : row 4 9=true := by decide +kernel
#print axioms row_4_9

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem row_5_8 : row 5 8=true := by decide +kernel
#print axioms row_5_8

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem row_5_9 : row 5 9=true := by decide +kernel
#print axioms row_5_9

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem row_6_9 : row 6 9=true := by decide +kernel
#print axioms row_6_9

end OffFour15
