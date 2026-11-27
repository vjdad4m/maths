import OffFour17Base189
namespace OffFour17
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
theorem row_3_4_8 : row 3 4 8=true := by decide +kernel
#print axioms row_3_4_8
end OffFour17
