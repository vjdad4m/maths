import OffFive17MarkedRow00012189
import OffFive17MarkedRow00112189
import OffFive17MarkedRow00122189
import OffFive17MarkedRow01112189
import OffFive17MarkedRow01122189
import OffFive17MarkedRow01222189
import OffFive17MarkedRow11112189
import OffFive17MarkedRow11122189
import OffFive17MarkedRow11222189
import OffFive17MarkedRow12222189
namespace OffFive17MarkedCore
private theorem colorTuples_exact :
    colorTuples=[[0,0,0,1,2],[0,0,1,1,2],[0,0,1,2,2],[0,1,1,1,2],[0,1,1,2,2],[0,1,2,2,2],[1,1,1,1,2],[1,1,1,2,2],[1,1,2,2,2],[1,2,2,2,2]]:= by decide +kernel

set_option maxHeartbeats 500000 in
theorem all_rows (P : List ℕ) (hm : P∈colorTuples) : row P=true := by
  rw [colorTuples_exact] at hm
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact row_00012
  · exact row_00112
  · exact row_00122
  · exact row_01112
  · exact row_01122
  · exact row_01222
  · exact row_11112
  · exact row_11122
  · exact row_11222
  · exact row_12222

#print axioms all_rows
end OffFive17MarkedCore
