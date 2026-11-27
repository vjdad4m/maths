import NestedCorePrivateExpandedSpec133
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

namespace Graffiti133ExpandedPrivate
open Graffiti133PrivateGeneric
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
def rowD_0_0_0 : Tree 19 := (.four 0 18 7 9)
theorem ok_rowD_0_0_0 : checked (dualSingleCase false 0) [] rowD_0_0_0=true := by decide

def rowD_0_0_1 : Tree 20 := (.four 0 18 7 19)
theorem ok_rowD_0_0_1 : checked (dualAdjacentCase false 0) [] rowD_0_0_1=true := by decide

def rowD_0_1_0 : Tree 19 := (.four 1 18 8 10)
theorem ok_rowD_0_1_0 : checked (dualSingleCase false 1) [] rowD_0_1_0=true := by decide

def rowD_0_1_1 : Tree 20 := (.four 1 18 8 19)
theorem ok_rowD_0_1_1 : checked (dualAdjacentCase false 1) [] rowD_0_1_1=true := by decide

def rowD_0_2_0 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 16 (.split 9 18 (.split 10 11 (.split 10 17 (.split 10 18 (.split 11 12 (.split 12 13 (.split 12 16 (.split 12 18 (.split 13 14 (.split 13 17 (.split 13 18 (.split 14 15 (.split 11 16 (.split 11 17 (.split 9 11 (.path ![2,11,18,8,4,5,6,0,9]) (.split 9 17 (.path ![2,11,9,0,6,5,4,8,17]) (.split 17 18 (.split 15 17 (.path ![2,3,4,8,17,9,0,6,15]) (.split 15 18 (.split 11 15 (.path ![0,6,15,17,8,18,11,2,3]) (.four 9 15 11 17)) (.four 8 15 17 18))) (.four 9 18 11 17)))) (.four 8 11 17 18)) (.four 7 11 16 18)) (.four 5 15 6 14)) (.four 4 18 8 13)) (.four 4 17 8 13)) (.four 4 14 5 13)) (.four 3 18 7 12)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 12 3 11)) (.four 1 18 8 10)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 18 7 9)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowD_0_2_0 : checked (dualSingleCase false 2) [] rowD_0_2_0=true := by decide

def rowD_0_2_1 : Tree 20 := (.four 3 18 7 19)
theorem ok_rowD_0_2_1 : checked (dualAdjacentCase false 2) [] rowD_0_2_1=true := by decide

def rowD_0_3_0 : Tree 19 := (.four 3 18 7 12)
theorem ok_rowD_0_3_0 : checked (dualSingleCase false 3) [] rowD_0_3_0=true := by decide

def rowD_0_3_1 : Tree 20 := (.four 3 18 7 19)
theorem ok_rowD_0_3_1 : checked (dualAdjacentCase false 3) [] rowD_0_3_1=true := by decide

def rowD_0_4_0 : Tree 19 := (.four 4 18 8 13)
theorem ok_rowD_0_4_0 : checked (dualSingleCase false 4) [] rowD_0_4_0=true := by decide

def rowD_0_4_1 : Tree 20 := (.four 4 18 8 19)
theorem ok_rowD_0_4_1 : checked (dualAdjacentCase false 4) [] rowD_0_4_1=true := by decide

def rowD_0_5_0 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 16 (.split 9 18 (.split 10 11 (.split 10 17 (.split 10 18 (.split 11 12 (.split 12 13 (.split 12 16 (.split 12 18 (.split 13 14 (.split 13 17 (.split 13 18 (.split 14 15 (.split 14 16 (.split 14 17 (.split 15 18 (.path ![1,2,3,7,18,14,5,6,15]) (.path ![0,1,2,3,4,5,14,18,15])) (.four 8 14 17 18)) (.four 7 14 16 18)) (.four 5 15 6 14)) (.four 4 18 8 13)) (.four 4 17 8 13)) (.four 4 14 5 13)) (.four 3 18 7 12)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 12 3 11)) (.four 1 18 8 10)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 18 7 9)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowD_0_5_0 : checked (dualSingleCase false 5) [] rowD_0_5_0=true := by decide

def rowD_0_5_1 : Tree 20 := (.split 9 10 (.split 9 15 (.split 9 19 (.split 9 16 (.split 9 18 (.split 10 11 (.split 10 17 (.split 10 18 (.split 11 12 (.split 12 13 (.split 12 16 (.split 12 18 (.split 13 14 (.split 13 19 (.split 13 17 (.split 13 18 (.split 14 15 (.split 14 19 (.split 15 19 (.split 14 18 (.split 15 18 (.split 16 19 (.split 17 19 (.split 11 19 (.split 11 18 (.path ![0,6,19,18,8,4,3,2,11]) (.split 11 16 (.split 11 17 (.split 11 13 (.path ![0,1,2,11,18,19,5,4,13]) (.split 12 19 (.path ![0,6,19,18,11,13,4,3,12]) (.path ![0,1,2,11,13,4,5,19,12]))) (.four 8 11 17 18)) (.four 7 11 16 18))) (.split 11 14 (.split 11 15 (.split 11 17 (.path ![0,6,19,11,2,3,4,8,17]) (.path ![1,0,7,3,4,5,19,11,17])) (.four 6 11 15 19)) (.four 5 11 14 19))) (.four 8 19 17 18)) (.four 7 19 16 18)) (.four 6 18 15 19)) (.four 5 18 14 19)) (.four 5 15 6 19)) (.four 5 19 6 14)) (.four 5 15 6 14)) (.four 4 18 8 13)) (.four 4 17 8 13)) (.four 4 19 5 13)) (.four 4 14 5 13)) (.four 3 18 7 12)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 12 3 11)) (.four 1 18 8 10)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 18 7 9)) (.four 0 16 7 9)) (.four 0 19 6 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowD_0_5_1 : checked (dualAdjacentCase false 5) [] rowD_0_5_1=true := by decide

def rowD_0_6_0 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 16 (.split 9 18 (.split 10 11 (.split 10 17 (.split 10 18 (.split 11 12 (.split 12 13 (.split 12 16 (.split 12 18 (.split 13 14 (.split 13 17 (.split 13 18 (.split 14 15 (.split 15 16 (.split 15 17 (.split 11 18 (.split 11 15 (.path ![0,6,15,18,8,4,3,2,11]) (.split 11 17 (.path ![0,6,15,11,2,3,4,8,17]) (.split 17 18 (.split 14 18 (.split 16 17 (.split 12 15 (.split 12 17 (.path ![0,6,15,11,17,8,4,3,12]) (.path ![0,6,15,18,8,17,12,3,2])) (.split 12 17 (.split 11 16 (.path ![1,8,17,11,15,12,3,7,16]) (.path ![0,1,8,4,3,12,15,11,16])) (.four 11 12 15 17))) (.split 16 18 (.split 11 16 (.path ![0,6,5,4,3,2,11,17,16]) (.split 12 15 (.split 12 17 (.path ![0,6,15,11,17,8,4,3,12]) (.path ![0,6,15,18,8,17,12,3,2])) (.path ![0,1,8,4,3,12,15,11,16]))) (.four 8 16 17 18))) (.split 14 16 (.split 14 17 (.split 11 14 (.split 12 15 (.split 12 17 (.path ![0,6,15,11,17,8,4,3,12]) (.path ![0,6,15,18,8,17,12,3,2])) (.split 12 17 (.split 12 14 (.split 11 16 (.split 16 17 (.path ![1,8,17,11,15,12,3,7,16]) (.path ![0,6,5,4,3,2,11,17,16])) (.path ![0,1,8,4,3,12,15,11,16])) (.four 12 18 14 15)) (.four 11 12 15 17))) (.four 11 18 14 15)) (.four 8 14 17 18)) (.four 7 14 16 18))) (.four 11 18 15 17)))) (.split 11 16 (.split 11 17 (.split 11 15 (.split 14 18 (.split 16 17 (.split 11 13 (.split 13 15 (.path ![0,6,15,18,11,2,3,4,13]) (.path ![0,1,2,11,18,15,13,4,5])) (.split 13 15 (.path ![1,0,6,15,18,11,13,4,3]) (.four 11 15 13 18))) (.split 17 18 (.split 16 18 (.split 11 13 (.split 13 15 (.path ![0,6,15,18,11,2,3,4,13]) (.path ![0,1,2,11,18,15,13,4,5])) (.split 13 15 (.path ![1,0,6,15,18,11,13,4,3]) (.four 11 15 13 18))) (.four 8 16 17 18)) (.four 7 17 16 18))) (.split 14 16 (.split 14 17 (.split 16 17 (.split 11 13 (.split 13 15 (.path ![0,6,15,18,11,2,3,4,13]) (.path ![0,1,2,11,18,15,13,4,5])) (.split 13 15 (.path ![1,0,6,15,18,11,13,4,3]) (.four 11 15 13 18))) (.split 17 18 (.split 16 18 (.split 11 13 (.split 13 15 (.path ![0,6,15,18,11,2,3,4,13]) (.path ![0,1,2,11,18,15,13,4,5])) (.split 13 15 (.path ![1,0,6,15,18,11,13,4,3]) (.four 11 15 13 18))) (.four 8 16 17 18)) (.four 7 17 16 18))) (.four 8 14 17 18)) (.four 7 14 16 18))) (.path ![0,6,15,11,2,3,4,8,17])) (.four 8 11 17 18)) (.four 7 11 16 18))) (.four 8 15 17 18)) (.four 7 15 16 18)) (.four 5 15 6 14)) (.four 4 18 8 13)) (.four 4 17 8 13)) (.four 4 14 5 13)) (.four 3 18 7 12)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 12 3 11)) (.four 1 18 8 10)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 18 7 9)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowD_0_6_0 : checked (dualSingleCase false 6) [] rowD_0_6_0=true := by decide

def rowD_0_6_1 : Tree 20 := (.four 0 18 7 19)
theorem ok_rowD_0_6_1 : checked (dualAdjacentCase false 6) [] rowD_0_6_1=true := by decide

def rowD_1_0_0 : Tree 19 := (.four 0 18 7 9)
theorem ok_rowD_1_0_0 : checked (dualSingleCase true 0) [] rowD_1_0_0=true := by decide

def rowD_1_0_1 : Tree 20 := (.four 0 18 7 19)
theorem ok_rowD_1_0_1 : checked (dualAdjacentCase true 0) [] rowD_1_0_1=true := by decide

def rowD_1_1_0 : Tree 19 := (.four 1 18 8 10)
theorem ok_rowD_1_1_0 : checked (dualSingleCase true 1) [] rowD_1_1_0=true := by decide

def rowD_1_1_1 : Tree 20 := (.four 1 2 8 19)
theorem ok_rowD_1_1_1 : checked (dualAdjacentCase true 1) [] rowD_1_1_1=true := by decide

def rowD_1_2_0 : Tree 19 := (.four 2 18 8 11)
theorem ok_rowD_1_2_0 : checked (dualSingleCase true 2) [] rowD_1_2_0=true := by decide

def rowD_1_2_1 : Tree 20 := (.four 2 18 8 19)
theorem ok_rowD_1_2_1 : checked (dualAdjacentCase true 2) [] rowD_1_2_1=true := by decide

def rowD_1_3_0 : Tree 19 := (.four 3 18 7 12)
theorem ok_rowD_1_3_0 : checked (dualSingleCase true 3) [] rowD_1_3_0=true := by decide

def rowD_1_3_1 : Tree 20 := (.four 3 18 7 19)
theorem ok_rowD_1_3_1 : checked (dualAdjacentCase true 3) [] rowD_1_3_1=true := by decide

def rowD_1_4_0 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 16 (.split 9 18 (.split 10 11 (.split 10 17 (.split 10 18 (.split 11 12 (.split 11 17 (.split 11 18 (.split 12 13 (.split 12 16 (.split 12 18 (.split 13 14 (.split 14 15 (.split 14 17 (.split 14 18 (.path ![2,1,0,7,18,13,4,5,14]) (.four 5 18 8 14)) (.four 5 17 8 14)) (.four 5 15 6 14)) (.four 4 14 5 13)) (.four 3 18 7 12)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 18 8 11)) (.four 2 17 8 11)) (.four 2 12 3 11)) (.four 1 18 8 10)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 18 7 9)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowD_1_4_0 : checked (dualSingleCase true 4) [] rowD_1_4_0=true := by decide

def rowD_1_4_1 : Tree 20 := (.four 5 18 8 19)
theorem ok_rowD_1_4_1 : checked (dualAdjacentCase true 4) [] rowD_1_4_1=true := by decide

def rowD_1_5_0 : Tree 19 := (.four 5 18 8 14)
theorem ok_rowD_1_5_0 : checked (dualSingleCase true 5) [] rowD_1_5_0=true := by decide

def rowD_1_5_1 : Tree 20 := (.four 5 18 8 19)
theorem ok_rowD_1_5_1 : checked (dualAdjacentCase true 5) [] rowD_1_5_1=true := by decide

def rowD_1_6_0 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 16 (.split 9 18 (.split 10 11 (.split 10 17 (.split 10 18 (.split 11 12 (.split 11 17 (.split 11 18 (.split 12 13 (.split 12 16 (.split 12 18 (.split 13 14 (.split 14 15 (.split 14 17 (.split 14 18 (.split 15 16 (.split 15 17 (.split 13 18 (.split 13 15 (.path ![0,6,15,18,8,2,3,4,13]) (.split 12 15 (.path ![0,1,8,18,15,13,4,3,12]) (.split 13 17 (.path ![0,6,15,13,4,3,2,8,17]) (.split 12 17 (.path ![0,7,3,12,15,13,17,8,5]) (.four 12 13 15 17))))) (.split 13 16 (.split 13 17 (.split 13 15 (.split 16 17 (.split 11 15 (.split 11 13 (.path ![0,6,15,18,13,4,3,2,11]) (.split 12 15 (.path ![0,6,15,18,13,11,2,3,12]) (.path ![1,0,6,15,12,3,4,13,11]))) (.split 11 13 (.path ![0,1,2,11,15,18,13,4,5]) (.four 11 18 13 15))) (.split 17 18 (.split 16 18 (.split 11 15 (.split 11 13 (.path ![0,6,15,18,13,4,3,2,11]) (.split 12 15 (.path ![0,6,15,18,13,11,2,3,12]) (.path ![1,0,6,15,12,3,4,13,11]))) (.split 11 13 (.path ![0,1,2,11,15,18,13,4,5]) (.four 11 18 13 15))) (.four 8 16 17 18)) (.four 7 17 16 18))) (.path ![0,6,15,13,4,3,2,8,17])) (.four 8 13 17 18)) (.four 7 13 16 18))) (.four 8 15 17 18)) (.four 7 15 16 18)) (.four 5 18 8 14)) (.four 5 17 8 14)) (.four 5 15 6 14)) (.four 4 14 5 13)) (.four 3 18 7 12)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 18 8 11)) (.four 2 17 8 11)) (.four 2 12 3 11)) (.four 1 18 8 10)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 18 7 9)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowD_1_6_0 : checked (dualSingleCase true 6) [] rowD_1_6_0=true := by decide

def rowD_1_6_1 : Tree 20 := (.four 0 18 7 19)
theorem ok_rowD_1_6_1 : checked (dualAdjacentCase true 6) [] rowD_1_6_1=true := by decide

theorem dual_single_all_rows (m : Bool) (i : Fin 7) :
    ∃ t : Tree 19,checked (dualSingleCase m i) [] t=true := by
  cases m <;> fin_cases i
  · exact ⟨rowD_0_0_0,ok_rowD_0_0_0⟩
  · exact ⟨rowD_0_1_0,ok_rowD_0_1_0⟩
  · exact ⟨rowD_0_2_0,ok_rowD_0_2_0⟩
  · exact ⟨rowD_0_3_0,ok_rowD_0_3_0⟩
  · exact ⟨rowD_0_4_0,ok_rowD_0_4_0⟩
  · exact ⟨rowD_0_5_0,ok_rowD_0_5_0⟩
  · exact ⟨rowD_0_6_0,ok_rowD_0_6_0⟩
  · exact ⟨rowD_1_0_0,ok_rowD_1_0_0⟩
  · exact ⟨rowD_1_1_0,ok_rowD_1_1_0⟩
  · exact ⟨rowD_1_2_0,ok_rowD_1_2_0⟩
  · exact ⟨rowD_1_3_0,ok_rowD_1_3_0⟩
  · exact ⟨rowD_1_4_0,ok_rowD_1_4_0⟩
  · exact ⟨rowD_1_5_0,ok_rowD_1_5_0⟩
  · exact ⟨rowD_1_6_0,ok_rowD_1_6_0⟩

theorem dual_adjacent_all_rows (m : Bool) (i : Fin 7) :
    ∃ t : Tree 20,checked (dualAdjacentCase m i) [] t=true := by
  cases m <;> fin_cases i
  · exact ⟨rowD_0_0_1,ok_rowD_0_0_1⟩
  · exact ⟨rowD_0_1_1,ok_rowD_0_1_1⟩
  · exact ⟨rowD_0_2_1,ok_rowD_0_2_1⟩
  · exact ⟨rowD_0_3_1,ok_rowD_0_3_1⟩
  · exact ⟨rowD_0_4_1,ok_rowD_0_4_1⟩
  · exact ⟨rowD_0_5_1,ok_rowD_0_5_1⟩
  · exact ⟨rowD_0_6_1,ok_rowD_0_6_1⟩
  · exact ⟨rowD_1_0_1,ok_rowD_1_0_1⟩
  · exact ⟨rowD_1_1_1,ok_rowD_1_1_1⟩
  · exact ⟨rowD_1_2_1,ok_rowD_1_2_1⟩
  · exact ⟨rowD_1_3_1,ok_rowD_1_3_1⟩
  · exact ⟨rowD_1_4_1,ok_rowD_1_4_1⟩
  · exact ⟨rowD_1_5_1,ok_rowD_1_5_1⟩
  · exact ⟨rowD_1_6_1,ok_rowD_1_6_1⟩
#print axioms dual_single_all_rows
#print axioms dual_adjacent_all_rows
end Graffiti133ExpandedPrivate
