import NestedCorePrivateExpandedSpec133
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

namespace Graffiti133ExpandedPrivate
open Graffiti133PrivateGeneric
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
def rowS_0_0_0_0_1 : Tree 19 := (.four 0 8 1 18)
theorem ok_rowS_0_0_0_0_1 : checked (singleCase false 0 0 false true) [] rowS_0_0_0_0_1=true := by decide

def rowS_0_0_0_1_0 : Tree 19 := (.four 0 16 7 18)
theorem ok_rowS_0_0_0_1_0 : checked (singleCase false 0 0 true false) [] rowS_0_0_0_1_0=true := by decide

def rowS_0_0_0_1_1 : Tree 19 := (.four 0 8 1 18)
theorem ok_rowS_0_0_0_1_1 : checked (singleCase false 0 0 true true) [] rowS_0_0_0_1_1=true := by decide

def rowS_0_0_1_0_1 : Tree 19 := (.split 9 10 (.split 9 18 (.split 9 15 (.split 9 16 (.split 10 11 (.split 11 18 (.split 10 17 (.split 10 18 (.split 17 18 (.split 10 16 (.split 11 12 (.split 12 13 (.split 12 16 (.split 13 14 (.split 13 17 (.split 13 18 (.split 14 15 (.split 16 17 (.split 15 18 (.split 15 16 (.path ![1,18,16,7,3,4,5,6,15]) (.path ![0,6,15,16,18,8,4,3,2])) (.split 10 15 (.split 15 17 (.split 11 15 (.path ![0,6,15,18,8,4,3,2,11]) (.split 11 16 (.split 11 17 (.path ![0,6,15,11,2,3,4,8,17]) (.split 14 18 (.split 12 18 (.split 12 15 (.split 12 17 (.path ![0,6,15,11,17,8,4,3,12]) (.path ![0,1,18,15,11,17,12,3,4])) (.split 12 17 (.split 12 14 (.path ![0,1,18,15,12,3,4,5,14]) (.split 11 14 (.path ![0,1,2,11,15,12,14,5,4]) (.four 11 12 14 15))) (.four 11 12 15 17))) (.split 10 12 (.split 12 17 (.split 12 15 (.path ![0,6,15,11,17,8,4,3,12]) (.split 15 16 (.path ![1,8,17,11,15,12,3,7,16]) (.four 12 16 15 18))) (.four 8 12 17 18)) (.four 1 12 10 18))) (.split 10 14 (.split 14 17 (.split 11 14 (.path ![0,6,5,14,18,8,17,11,2]) (.four 11 18 14 15)) (.four 8 14 17 18)) (.four 1 14 10 18)))) (.four 11 18 15 16))) (.four 8 15 17 18)) (.four 1 15 10 18))) (.four 8 16 17 18)) (.four 5 15 6 14)) (.four 4 18 8 13)) (.four 4 17 8 13)) (.four 4 14 5 13)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 12 3 11)) (.four 1 16 10 18)) (.four 1 17 8 18)) (.four 1 18 8 10)) (.four 1 17 8 10)) (.four 1 11 2 18)) (.four 1 11 2 10)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 18 1 9)) (.four 0 10 1 9))
theorem ok_rowS_0_0_1_0_1 : checked (singleCase false 0 1 false true) [] rowS_0_0_1_0_1=true := by decide

def rowS_0_0_1_1_0 : Tree 19 := (.split 9 10 (.split 9 18 (.split 9 15 (.split 9 16 (.split 10 11 (.split 10 18 (.split 11 18 (.split 10 17 (.split 17 18 (.split 10 16 (.split 11 12 (.split 12 18 (.split 11 16 (.split 12 13 (.split 12 16 (.split 13 14 (.split 13 17 (.split 14 15 (.split 11 17 (.split 15 18 (.split 15 16 (.path ![1,18,16,7,3,4,5,6,15]) (.path ![0,6,15,16,18,2,3,4,8])) (.split 10 15 (.split 11 15 (.split 15 17 (.path ![0,6,15,18,2,3,4,8,17]) (.path ![0,6,15,17,8,4,3,2,11])) (.four 2 15 11 18)) (.four 1 15 10 18))) (.path ![0,6,5,4,8,17,11,2,18])) (.four 5 15 6 14)) (.four 4 17 8 13)) (.four 4 14 5 13)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 16 11 18)) (.four 2 12 3 18)) (.four 2 12 3 11)) (.four 1 16 10 18)) (.four 1 17 8 18)) (.four 1 17 8 10)) (.four 1 11 2 18)) (.four 1 18 2 10)) (.four 1 11 2 10)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 18 1 9)) (.four 0 10 1 9))
theorem ok_rowS_0_0_1_1_0 : checked (singleCase false 0 1 true false) [] rowS_0_0_1_1_0=true := by decide

def rowS_0_0_1_1_1 : Tree 19 := (.four 1 18 2 8)
theorem ok_rowS_0_0_1_1_1 : checked (singleCase false 0 1 true true) [] rowS_0_0_1_1_1=true := by decide

def rowS_0_0_2_0_1 : Tree 19 := (.four 1 18 2 8)
theorem ok_rowS_0_0_2_0_1 : checked (singleCase false 0 2 false true) [] rowS_0_0_2_0_1=true := by decide

def rowS_0_0_2_1_0 : Tree 19 := (.four 3 16 7 18)
theorem ok_rowS_0_0_2_1_0 : checked (singleCase false 0 2 true false) [] rowS_0_0_2_1_0=true := by decide

def rowS_0_0_2_1_1 : Tree 19 := (.four 1 18 2 8)
theorem ok_rowS_0_0_2_1_1 : checked (singleCase false 0 2 true true) [] rowS_0_0_2_1_1=true := by decide

def rowS_0_0_3_0_1 : Tree 19 := (.four 3 8 4 18)
theorem ok_rowS_0_0_3_0_1 : checked (singleCase false 0 3 false true) [] rowS_0_0_3_0_1=true := by decide

def rowS_0_0_3_1_0 : Tree 19 := (.four 3 16 7 18)
theorem ok_rowS_0_0_3_1_0 : checked (singleCase false 0 3 true false) [] rowS_0_0_3_1_0=true := by decide

def rowS_0_0_3_1_1 : Tree 19 := (.four 3 8 4 18)
theorem ok_rowS_0_0_3_1_1 : checked (singleCase false 0 3 true true) [] rowS_0_0_3_1_1=true := by decide

def rowS_0_0_4_0_1 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 16 (.split 10 11 (.split 10 17 (.split 10 18 (.split 11 12 (.split 12 13 (.split 12 18 (.split 12 16 (.split 13 14 (.split 14 18 (.split 13 17 (.split 13 18 (.split 17 18 (.split 13 16 (.split 14 15 (.split 16 17 (.split 14 16 (.path ![2,1,0,7,16,18,4,5,14]) (.split 15 16 (.path ![1,2,3,7,16,14,5,6,15]) (.path ![0,1,2,3,4,5,14,16,15]))) (.four 8 16 17 18)) (.four 5 15 6 14)) (.four 4 16 13 18)) (.four 4 17 8 18)) (.four 4 18 8 13)) (.four 4 17 8 13)) (.four 4 14 5 18)) (.four 4 14 5 13)) (.four 3 16 7 12)) (.four 3 18 4 12)) (.four 3 13 4 12)) (.four 2 12 3 11)) (.four 1 18 8 10)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowS_0_0_4_0_1 : checked (singleCase false 0 4 false true) [] rowS_0_0_4_0_1=true := by decide

def rowS_0_0_4_1_0 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 16 (.split 10 11 (.split 10 17 (.split 11 12 (.split 12 13 (.split 12 18 (.split 12 16 (.split 13 14 (.split 13 18 (.split 14 18 (.split 13 17 (.split 17 18 (.split 13 16 (.split 14 15 (.split 15 18 (.split 14 16 (.split 15 16 (.path ![1,2,3,7,16,18,5,6,15]) (.split 12 15 (.split 10 18 (.split 11 18 (.split 11 16 (.split 11 15 (.path ![0,6,15,16,18,4,3,2,11]) (.split 11 14 (.path ![0,1,2,11,15,16,18,5,14]) (.path ![0,1,8,4,5,14,11,15,16]))) (.path ![0,6,5,18,16,11,2,3,12])) (.split 11 13 (.split 11 14 (.split 11 15 (.split 11 16 (.path ![0,6,15,16,18,11,2,3,12]) (.path ![0,6,15,16,11,2,3,4,8])) (.four 11 16 15 18)) (.four 5 11 14 18)) (.four 4 11 13 18))) (.split 10 13 (.split 10 14 (.split 10 15 (.split 11 18 (.split 11 16 (.split 11 15 (.path ![0,6,15,16,18,4,3,2,11]) (.split 11 14 (.path ![0,1,2,11,15,16,18,5,14]) (.path ![0,1,8,4,5,14,11,15,16]))) (.path ![0,6,5,18,16,11,2,3,12])) (.split 11 13 (.split 11 14 (.split 11 15 (.split 11 16 (.path ![0,6,15,16,18,11,2,3,12]) (.path ![0,6,15,16,11,2,3,4,8])) (.four 11 16 15 18)) (.four 5 11 14 18)) (.four 4 11 13 18))) (.four 10 16 15 18)) (.four 5 10 14 18)) (.four 4 10 13 18))) (.path ![0,1,2,3,12,15,16,18,5]))) (.four 5 16 14 18)) (.four 5 15 6 18)) (.four 5 15 6 14)) (.four 4 16 13 18)) (.four 4 17 8 18)) (.four 4 17 8 13)) (.four 4 14 5 18)) (.four 4 18 5 13)) (.four 4 14 5 13)) (.four 3 16 7 12)) (.four 3 18 4 12)) (.four 3 13 4 12)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowS_0_0_4_1_0 : checked (singleCase false 0 4 true false) [] rowS_0_0_4_1_0=true := by decide

def rowS_0_0_4_1_1 : Tree 19 := (.four 4 18 5 8)
theorem ok_rowS_0_0_4_1_1 : checked (singleCase false 0 4 true true) [] rowS_0_0_4_1_1=true := by decide

def rowS_0_0_5_0_1 : Tree 19 := (.four 4 18 5 8)
theorem ok_rowS_0_0_5_0_1 : checked (singleCase false 0 5 false true) [] rowS_0_0_5_0_1=true := by decide

def rowS_0_0_5_1_0 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 18 (.split 9 16 (.split 10 11 (.split 10 17 (.split 11 12 (.split 12 13 (.split 12 16 (.split 13 14 (.split 13 18 (.split 13 17 (.split 14 15 (.split 14 18 (.split 15 18 (.split 14 16 (.split 15 16 (.path ![1,8,4,3,7,16,18,6,15]) (.four 6 16 15 18)) (.four 5 16 14 18)) (.four 5 15 6 18)) (.four 5 18 6 14)) (.four 5 15 6 14)) (.four 4 17 8 13)) (.four 4 18 5 13)) (.four 4 14 5 13)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 16 7 9)) (.four 0 18 6 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowS_0_0_5_1_0 : checked (singleCase false 0 5 true false) [] rowS_0_0_5_1_0=true := by decide

def rowS_0_0_5_1_1 : Tree 19 := (.four 4 18 5 8)
theorem ok_rowS_0_0_5_1_1 : checked (singleCase false 0 5 true true) [] rowS_0_0_5_1_1=true := by decide

def rowS_0_0_6_0_1 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 18 (.split 9 16 (.split 10 11 (.split 10 17 (.split 10 18 (.split 11 12 (.split 12 13 (.split 12 16 (.split 13 14 (.split 13 17 (.split 13 18 (.split 14 15 (.split 14 18 (.split 15 16 (.split 16 17 (.split 14 16 (.path ![1,2,3,7,16,18,6,5,14]) (.path ![0,1,2,3,4,5,14,16,18])) (.four 8 16 17 18)) (.four 6 16 15 18)) (.four 5 18 6 14)) (.four 5 15 6 14)) (.four 4 18 8 13)) (.four 4 17 8 13)) (.four 4 14 5 13)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 12 3 11)) (.four 1 18 8 10)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 16 7 9)) (.four 0 18 6 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowS_0_0_6_0_1 : checked (singleCase false 0 6 false true) [] rowS_0_0_6_0_1=true := by decide

def rowS_0_0_6_1_0 : Tree 19 := (.four 0 16 7 18)
theorem ok_rowS_0_0_6_1_0 : checked (singleCase false 0 6 true false) [] rowS_0_0_6_1_0=true := by decide

def rowS_0_0_6_1_1 : Tree 19 := (.four 0 8 1 18)
theorem ok_rowS_0_0_6_1_1 : checked (singleCase false 0 6 true true) [] rowS_0_0_6_1_1=true := by decide

def rowS_0_1_0_0_1 : Tree 19 := (.split 9 10 (.split 10 18 (.split 9 15 (.split 15 18 (.split 9 16 (.split 9 18 (.split 16 18 (.split 9 17 (.split 10 11 (.split 10 17 (.split 11 12 (.split 12 13 (.split 12 16 (.split 12 18 (.split 13 14 (.split 13 17 (.split 14 15 (.split 16 17 (.split 15 17 (.path ![2,3,4,8,17,18,0,6,15]) (.split 14 17 (.split 11 18 (.split 13 18 (.split 14 18 (.split 11 17 (.split 11 15 (.path ![0,6,15,17,8,4,3,2,11]) (.path ![0,18,17,15,11,2,3,4,5])) (.split 11 14 (.path ![0,18,17,11,2,3,4,5,14]) (.split 11 15 (.path ![0,7,3,4,5,14,11,17,15]) (.split 12 17 (.split 12 14 (.path ![0,18,17,11,14,5,4,3,12]) (.split 12 15 (.path ![0,1,8,4,3,12,14,11,15]) (.four 11 12 14 15))) (.path ![1,0,6,5,4,3,12,17,11]))))) (.split 9 14 (.split 14 16 (.split 11 17 (.split 11 15 (.path ![0,6,15,17,8,4,3,2,11]) (.path ![0,18,17,15,11,2,3,4,5])) (.split 11 14 (.split 12 17 (.split 11 15 (.split 11 13 (.split 13 15 (.path ![0,6,15,17,11,2,3,4,13]) (.path ![0,1,2,11,17,15,13,4,5])) (.split 13 15 (.path ![1,0,6,15,17,11,13,4,3]) (.four 11 15 13 17))) (.path ![0,18,14,5,4,3,2,11,15])) (.path ![1,0,6,5,4,3,12,17,11])) (.four 11 18 14 17))) (.four 7 14 16 18)) (.four 0 14 9 18))) (.split 9 13 (.split 13 16 (.split 13 15 (.split 14 18 (.split 11 17 (.split 11 15 (.path ![0,6,15,17,8,4,3,2,11]) (.path ![0,18,17,15,11,2,3,4,5])) (.split 11 13 (.split 11 15 (.path ![0,6,15,17,11,2,3,4,13]) (.split 11 14 (.path ![0,18,17,11,2,3,4,5,14]) (.split 12 17 (.split 12 14 (.path ![0,18,17,11,14,5,4,3,12]) (.split 12 15 (.path ![0,1,8,4,3,12,14,11,15]) (.four 11 12 14 15))) (.path ![1,0,6,5,4,3,12,17,11])))) (.four 11 18 13 17))) (.split 9 14 (.split 14 16 (.split 11 17 (.split 11 15 (.path ![0,6,15,17,8,4,3,2,11]) (.path ![0,18,17,15,11,2,3,4,5])) (.split 11 13 (.split 11 14 (.split 11 15 (.path ![0,6,15,17,11,2,3,4,13]) (.path ![0,18,14,5,4,3,2,11,15])) (.four 11 18 14 17)) (.four 11 18 13 17))) (.four 7 14 16 18)) (.four 0 14 9 18))) (.four 13 17 15 18)) (.four 7 13 16 18)) (.four 0 13 9 18))) (.split 9 11 (.split 11 16 (.split 11 15 (.split 11 17 (.path ![0,6,15,17,8,4,3,2,11]) (.split 11 14 (.split 12 17 (.split 13 18 (.split 14 18 (.split 11 13 (.split 13 15 (.path ![0,6,15,17,11,2,3,4,13]) (.path ![0,1,2,11,17,15,13,4,5])) (.split 13 15 (.path ![1,0,6,15,17,11,13,4,3]) (.four 11 15 13 17))) (.split 9 14 (.split 14 16 (.split 11 13 (.split 13 15 (.path ![0,6,15,17,11,2,3,4,13]) (.path ![0,1,2,11,17,15,13,4,5])) (.split 13 15 (.path ![1,0,6,15,17,11,13,4,3]) (.four 11 15 13 17))) (.four 7 14 16 18)) (.four 0 14 9 18))) (.split 9 13 (.split 13 16 (.split 11 13 (.split 13 15 (.path ![0,6,15,17,11,2,3,4,13]) (.four 13 17 15 18)) (.four 11 18 13 17)) (.four 7 13 16 18)) (.four 0 13 9 18))) (.path ![1,0,6,5,4,3,12,17,11])) (.path ![0,7,3,4,5,14,11,17,15]))) (.four 11 17 15 18)) (.four 7 11 16 18)) (.four 0 11 9 18))) (.path ![0,1,2,3,4,5,14,17,15]))) (.four 7 17 16 18)) (.four 5 15 6 14)) (.four 4 17 8 13)) (.four 4 14 5 13)) (.four 3 18 7 12)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 17 9 18)) (.four 0 16 7 18)) (.four 0 18 7 9)) (.four 0 16 7 9)) (.four 0 15 6 18)) (.four 0 15 6 9)) (.four 0 10 1 18)) (.four 0 10 1 9))
theorem ok_rowS_0_1_0_0_1 : checked (singleCase false 1 0 false true) [] rowS_0_1_0_0_1=true := by decide

def rowS_0_1_0_1_0 : Tree 19 := (.four 1 17 8 18)
theorem ok_rowS_0_1_0_1_0 : checked (singleCase false 1 0 true false) [] rowS_0_1_0_1_0=true := by decide

def rowS_0_1_0_1_1 : Tree 19 := (.four 0 18 1 7)
theorem ok_rowS_0_1_0_1_1 : checked (singleCase false 1 0 true true) [] rowS_0_1_0_1_1=true := by decide

def rowS_0_1_1_0_1 : Tree 19 := (.four 0 18 1 7)
theorem ok_rowS_0_1_1_0_1 : checked (singleCase false 1 1 false true) [] rowS_0_1_1_0_1=true := by decide

def rowS_0_1_1_1_0 : Tree 19 := (.four 1 17 8 18)
theorem ok_rowS_0_1_1_1_0 : checked (singleCase false 1 1 true false) [] rowS_0_1_1_1_0=true := by decide

def rowS_0_1_1_1_1 : Tree 19 := (.four 0 18 1 7)
theorem ok_rowS_0_1_1_1_1 : checked (singleCase false 1 1 true true) [] rowS_0_1_1_1_1=true := by decide

def rowS_0_1_2_0_1 : Tree 19 := (.four 2 7 3 18)
theorem ok_rowS_0_1_2_0_1 : checked (singleCase false 1 2 false true) [] rowS_0_1_2_0_1=true := by decide

def rowS_0_1_2_1_0 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 16 (.split 10 11 (.split 10 18 (.split 10 17 (.split 11 12 (.split 11 18 (.split 12 18 (.split 11 17 (.path ![0,6,5,4,8,17,18,2,11]) (.four 2 17 11 18)) (.four 2 12 3 18)) (.four 2 18 3 11)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 18 2 10)) (.four 1 11 2 10)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowS_0_1_2_1_0 : checked (singleCase false 1 2 true false) [] rowS_0_1_2_1_0=true := by decide

def rowS_0_1_2_1_1 : Tree 19 := (.four 2 7 3 18)
theorem ok_rowS_0_1_2_1_1 : checked (singleCase false 1 2 true true) [] rowS_0_1_2_1_1=true := by decide

def rowS_0_1_3_0_1 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 16 (.split 9 18 (.split 10 11 (.split 10 17 (.split 11 12 (.split 11 18 (.split 12 13 (.split 13 18 (.split 12 16 (.split 12 18 (.split 16 18 (.split 12 17 (.split 13 14 (.split 13 17 (.split 14 15 (.split 16 17 (.split 14 18 (.split 14 17 (.path ![3,18,17,8,1,0,6,5,14]) (.path ![1,0,7,18,17,14,5,4,13])) (.path ![2,1,0,7,18,14,5,4,13])) (.four 7 17 16 18)) (.four 5 15 6 14)) (.four 4 17 8 13)) (.four 4 14 5 13)) (.four 3 17 12 18)) (.four 3 16 7 18)) (.four 3 18 7 12)) (.four 3 16 7 12)) (.four 3 13 4 18)) (.four 3 13 4 12)) (.four 2 18 3 11)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 18 7 9)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowS_0_1_3_0_1 : checked (singleCase false 1 3 false true) [] rowS_0_1_3_0_1=true := by decide

def rowS_0_1_3_1_0 : Tree 19 := (.four 4 17 8 18)
theorem ok_rowS_0_1_3_1_0 : checked (singleCase false 1 3 true false) [] rowS_0_1_3_1_0=true := by decide

def rowS_0_1_3_1_1 : Tree 19 := (.four 3 18 4 7)
theorem ok_rowS_0_1_3_1_1 : checked (singleCase false 1 3 true true) [] rowS_0_1_3_1_1=true := by decide

def rowS_0_1_4_0_1 : Tree 19 := (.four 3 18 4 7)
theorem ok_rowS_0_1_4_0_1 : checked (singleCase false 1 4 false true) [] rowS_0_1_4_0_1=true := by decide

def rowS_0_1_4_1_0 : Tree 19 := (.four 4 17 8 18)
theorem ok_rowS_0_1_4_1_0 : checked (singleCase false 1 4 true false) [] rowS_0_1_4_1_0=true := by decide

def rowS_0_1_4_1_1 : Tree 19 := (.four 3 18 4 7)
theorem ok_rowS_0_1_4_1_1 : checked (singleCase false 1 4 true true) [] rowS_0_1_4_1_1=true := by decide

def rowS_0_1_5_0_1 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 16 (.split 9 18 (.split 10 11 (.split 10 17 (.split 11 12 (.split 12 13 (.split 12 16 (.split 12 18 (.split 13 14 (.split 13 18 (.split 13 17 (.split 14 15 (.split 15 18 (.split 14 17 (.split 16 17 (.split 15 17 (.path ![3,2,1,8,17,18,5,6,15]) (.path ![0,1,2,3,4,5,18,17,15])) (.four 7 17 16 18)) (.four 5 17 14 18)) (.four 5 15 6 18)) (.four 5 15 6 14)) (.four 4 17 8 13)) (.four 4 18 5 13)) (.four 4 14 5 13)) (.four 3 18 7 12)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 18 7 9)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowS_0_1_5_0_1 : checked (singleCase false 1 5 false true) [] rowS_0_1_5_0_1=true := by decide

def rowS_0_1_5_1_0 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 18 (.split 9 16 (.split 10 11 (.split 10 17 (.split 11 12 (.split 12 13 (.split 12 16 (.split 13 14 (.split 13 18 (.split 13 17 (.split 14 15 (.split 14 18 (.split 15 18 (.split 14 17 (.split 15 17 (.split 9 17 (.path ![2,3,4,8,17,18,6,0,9]) (.split 11 18 (.split 11 17 (.path ![0,6,18,17,8,4,3,2,11]) (.split 11 13 (.path ![0,1,2,11,17,18,5,4,13]) (.split 9 13 (.split 12 18 (.split 12 17 (.path ![0,6,18,17,11,13,4,3,12]) (.path ![1,0,6,18,17,12,3,4,13])) (.path ![0,1,2,11,13,4,5,18,12])) (.four 9 11 13 17)))) (.split 11 14 (.split 11 15 (.split 9 11 (.split 12 18 (.split 9 12 (.split 12 17 (.path ![1,0,9,17,18,5,4,3,12]) (.path ![1,0,6,18,17,12,3,4,13])) (.path ![1,0,9,12,3,4,5,18,11])) (.split 12 14 (.split 12 15 (.split 9 12 (.split 10 18 (.split 16 18 (.split 11 17 (.split 11 13 (.split 9 13 (.path ![0,9,17,18,11,2,3,4,13]) (.path ![1,0,9,13,4,3,12,18,11])) (.path ![1,0,7,3,4,13,11,18,17])) (.split 12 17 (.split 9 14 (.path ![0,9,17,11,2,3,4,5,14]) (.split 9 13 (.path ![1,0,9,17,18,12,3,4,13]) (.split 11 13 (.path ![1,0,9,13,4,3,12,18,11]) (.four 9 11 13 17)))) (.four 11 12 17 18))) (.split 14 16 (.split 15 16 (.split 11 17 (.split 11 13 (.split 9 13 (.path ![0,9,17,18,11,2,3,4,13]) (.path ![1,0,9,13,4,3,12,18,11])) (.path ![1,0,7,3,4,13,11,18,17])) (.split 12 17 (.split 16 17 (.split 11 16 (.split 9 14 (.path ![0,9,17,11,2,3,4,5,14]) (.split 9 13 (.path ![1,0,9,17,18,12,3,4,13]) (.split 11 13 (.path ![1,0,9,13,4,3,12,18,11]) (.four 9 11 13 17)))) (.four 11 18 16 17)) (.four 11 16 17 18)) (.four 11 12 17 18))) (.four 6 16 15 18)) (.four 5 16 14 18))) (.split 10 14 (.split 10 15 (.split 16 18 (.split 11 13 (.split 9 13 (.split 11 17 (.path ![0,9,17,18,11,2,3,4,13]) (.split 12 17 (.path ![1,0,9,17,18,12,3,4,13]) (.four 11 12 17 18))) (.path ![1,0,9,13,4,3,12,18,11])) (.split 10 13 (.split 11 17 (.path ![1,0,7,3,4,13,11,18,17]) (.split 9 13 (.split 12 17 (.path ![1,0,9,17,18,12,3,4,13]) (.four 11 12 17 18)) (.four 9 11 13 17))) (.four 10 11 13 18))) (.split 14 16 (.split 15 16 (.split 16 17 (.split 11 13 (.split 9 13 (.split 11 17 (.path ![0,9,17,18,11,2,3,4,13]) (.split 12 17 (.path ![1,0,9,17,18,12,3,4,13]) (.four 11 12 17 18))) (.path ![1,0,9,13,4,3,12,18,11])) (.split 10 13 (.split 13 16 (.split 11 17 (.path ![1,0,7,3,4,13,11,18,17]) (.split 9 13 (.split 12 17 (.path ![1,0,9,17,18,12,3,4,13]) (.four 11 12 17 18)) (.four 9 11 13 17))) (.four 11 16 13 18)) (.four 10 11 13 18))) (.split 10 16 (.split 11 16 (.split 11 17 (.split 12 17 (.split 11 13 (.split 9 13 (.path ![0,9,17,18,11,2,3,4,13]) (.path ![1,0,9,13,4,3,12,18,11])) (.path ![1,0,7,3,4,13,11,18,17])) (.four 12 16 17 18)) (.four 11 16 17 18)) (.four 11 17 16 18)) (.four 10 17 16 18))) (.four 6 16 15 18)) (.four 5 16 14 18))) (.four 6 10 15 18)) (.four 5 10 14 18))) (.four 9 18 12 17)) (.four 6 12 15 18)) (.four 5 12 14 18))) (.four 9 18 11 17)) (.four 6 11 15 18)) (.four 5 11 14 18)))) (.four 6 17 15 18)) (.four 5 17 14 18)) (.four 5 15 6 18)) (.four 5 18 6 14)) (.four 5 15 6 14)) (.four 4 17 8 13)) (.four 4 18 5 13)) (.four 4 14 5 13)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 16 7 9)) (.four 0 18 6 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowS_0_1_5_1_0 : checked (singleCase false 1 5 true false) [] rowS_0_1_5_1_0=true := by decide

def rowS_0_1_5_1_1 : Tree 19 := (.four 0 18 6 7)
theorem ok_rowS_0_1_5_1_1 : checked (singleCase false 1 5 true true) [] rowS_0_1_5_1_1=true := by decide

def rowS_0_1_6_0_1 : Tree 19 := (.four 0 18 6 7)
theorem ok_rowS_0_1_6_0_1 : checked (singleCase false 1 6 false true) [] rowS_0_1_6_0_1=true := by decide

def rowS_0_1_6_1_0 : Tree 19 := (.split 9 10 (.split 10 18 (.split 9 15 (.split 9 18 (.split 15 18 (.split 9 16 (.split 16 18 (.split 9 17 (.split 10 11 (.split 10 17 (.split 11 12 (.split 12 13 (.split 12 16 (.split 13 14 (.split 13 17 (.split 14 15 (.split 14 18 (.split 15 17 (.split 14 17 (.path ![3,2,1,8,17,18,6,5,14]) (.split 9 14 (.path ![2,3,4,5,14,17,18,0,9]) (.split 11 18 (.split 12 18 (.split 13 18 (.split 11 17 (.split 11 14 (.path ![0,18,17,14,5,4,3,2,11]) (.split 11 13 (.path ![0,18,17,14,11,2,3,4,13]) (.path ![1,0,7,3,4,13,11,14,17]))) (.split 9 11 (.split 12 17 (.split 12 14 (.path ![1,0,18,17,14,5,4,3,12]) (.path ![1,0,18,17,14,12,3,4,13])) (.path ![1,0,6,5,4,3,12,17,11])) (.four 9 17 11 14))) (.split 9 13 (.split 13 15 (.split 11 17 (.split 11 14 (.path ![0,18,17,14,5,4,3,2,11]) (.split 11 13 (.split 12 14 (.split 12 17 (.path ![1,0,18,17,14,5,4,3,12]) (.split 9 12 (.split 12 15 (.path ![1,2,3,12,17,14,5,6,15]) (.path ![1,0,9,14,5,4,3,12,15])) (.four 9 17 12 14))) (.path ![1,0,18,13,4,3,12,14,11])) (.path ![1,0,7,3,4,13,11,14,17]))) (.split 9 11 (.split 11 13 (.split 11 14 (.path ![0,1,2,11,17,14,5,4,13]) (.split 12 17 (.split 12 14 (.path ![1,0,18,17,14,5,4,3,12]) (.path ![1,0,18,13,4,3,12,14,11])) (.path ![1,0,6,5,4,3,12,17,11]))) (.four 11 18 13 17)) (.four 9 17 11 14))) (.four 6 13 15 18)) (.four 0 13 9 18))) (.split 9 12 (.split 12 15 (.split 12 14 (.split 12 17 (.split 11 14 (.split 11 17 (.path ![0,18,17,14,5,4,3,2,11]) (.path ![0,6,5,14,17,11,2,3,12])) (.path ![1,0,18,12,3,4,5,14,11])) (.path ![1,2,3,12,17,14,5,6,15])) (.four 12 17 14 18)) (.four 6 12 15 18)) (.four 0 12 9 18))) (.split 9 11 (.split 11 15 (.split 11 14 (.split 11 17 (.path ![0,9,14,17,8,4,3,2,11]) (.split 11 13 (.path ![0,1,2,11,17,14,5,4,13]) (.split 13 18 (.split 12 17 (.split 12 14 (.path ![0,6,5,14,17,11,2,3,12]) (.split 12 18 (.path ![1,0,18,17,14,12,3,4,13]) (.four 12 17 14 18))) (.path ![1,0,6,5,4,3,12,17,11])) (.four 11 18 13 17)))) (.four 11 17 14 18)) (.four 6 11 15 18)) (.four 0 11 9 18))))) (.four 6 17 15 18)) (.four 5 18 6 14)) (.four 5 15 6 14)) (.four 4 17 8 13)) (.four 4 14 5 13)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 17 9 18)) (.four 0 16 7 18)) (.four 0 16 7 9)) (.four 0 15 6 18)) (.four 0 18 6 9)) (.four 0 15 6 9)) (.four 0 10 1 18)) (.four 0 10 1 9))
theorem ok_rowS_0_1_6_1_0 : checked (singleCase false 1 6 true false) [] rowS_0_1_6_1_0=true := by decide

def rowS_0_1_6_1_1 : Tree 19 := (.four 0 18 6 7)
theorem ok_rowS_0_1_6_1_1 : checked (singleCase false 1 6 true true) [] rowS_0_1_6_1_1=true := by decide

def rowS_1_0_0_0_1 : Tree 19 := (.four 0 8 1 18)
theorem ok_rowS_1_0_0_0_1 : checked (singleCase true 0 0 false true) [] rowS_1_0_0_0_1=true := by decide

def rowS_1_0_0_1_0 : Tree 19 := (.four 0 16 7 18)
theorem ok_rowS_1_0_0_1_0 : checked (singleCase true 0 0 true false) [] rowS_1_0_0_1_0=true := by decide

def rowS_1_0_0_1_1 : Tree 19 := (.four 0 8 1 18)
theorem ok_rowS_1_0_0_1_1 : checked (singleCase true 0 0 true true) [] rowS_1_0_0_1_1=true := by decide

def rowS_1_0_1_0_1 : Tree 19 := (.four 1 8 2 18)
theorem ok_rowS_1_0_1_0_1 : checked (singleCase true 0 1 false true) [] rowS_1_0_1_0_1=true := by decide

def rowS_1_0_1_1_0 : Tree 19 := (.four 1 2 8 18)
theorem ok_rowS_1_0_1_1_0 : checked (singleCase true 0 1 true false) [] rowS_1_0_1_1_0=true := by decide

def rowS_1_0_1_1_1 : Tree 19 := (.four 1 8 2 18)
theorem ok_rowS_1_0_1_1_1 : checked (singleCase true 0 1 true true) [] rowS_1_0_1_1_1=true := by decide

def rowS_1_0_2_0_1 : Tree 19 := (.four 1 18 2 8)
theorem ok_rowS_1_0_2_0_1 : checked (singleCase true 0 2 false true) [] rowS_1_0_2_0_1=true := by decide

def rowS_1_0_2_1_0 : Tree 19 := (.four 3 16 7 18)
theorem ok_rowS_1_0_2_1_0 : checked (singleCase true 0 2 true false) [] rowS_1_0_2_1_0=true := by decide

def rowS_1_0_2_1_1 : Tree 19 := (.four 1 18 2 8)
theorem ok_rowS_1_0_2_1_1 : checked (singleCase true 0 2 true true) [] rowS_1_0_2_1_1=true := by decide

def rowS_1_0_3_0_1 : Tree 19 := (.four 2 18 3 8)
theorem ok_rowS_1_0_3_0_1 : checked (singleCase true 0 3 false true) [] rowS_1_0_3_0_1=true := by decide

def rowS_1_0_3_1_0 : Tree 19 := (.four 3 16 7 18)
theorem ok_rowS_1_0_3_1_0 : checked (singleCase true 0 3 true false) [] rowS_1_0_3_1_0=true := by decide

def rowS_1_0_3_1_1 : Tree 19 := (.four 2 18 3 8)
theorem ok_rowS_1_0_3_1_1 : checked (singleCase true 0 3 true true) [] rowS_1_0_3_1_1=true := by decide

def rowS_1_0_4_0_1 : Tree 19 := (.four 4 8 5 18)
theorem ok_rowS_1_0_4_0_1 : checked (singleCase true 0 4 false true) [] rowS_1_0_4_0_1=true := by decide

def rowS_1_0_4_1_0 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 16 (.split 10 11 (.split 10 17 (.split 11 12 (.split 11 17 (.split 12 13 (.split 12 18 (.split 12 16 (.split 13 14 (.split 13 18 (.split 14 18 (.split 13 16 (.split 14 15 (.split 15 18 (.split 14 17 (.split 17 18 (.split 14 16 (.split 15 16 (.path ![1,2,3,7,16,18,5,6,15]) (.path ![0,6,15,16,18,4,3,2,8])) (.four 5 16 14 18)) (.four 5 17 8 18)) (.four 5 17 8 14)) (.four 5 15 6 18)) (.four 5 15 6 14)) (.four 4 16 13 18)) (.four 4 14 5 18)) (.four 4 18 5 13)) (.four 4 14 5 13)) (.four 3 16 7 12)) (.four 3 18 4 12)) (.four 3 13 4 12)) (.four 2 17 8 11)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowS_1_0_4_1_0 : checked (singleCase true 0 4 true false) [] rowS_1_0_4_1_0=true := by decide

def rowS_1_0_4_1_1 : Tree 19 := (.four 4 8 5 18)
theorem ok_rowS_1_0_4_1_1 : checked (singleCase true 0 4 true true) [] rowS_1_0_4_1_1=true := by decide

def rowS_1_0_5_0_1 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 16 (.split 10 11 (.split 10 17 (.split 10 18 (.split 11 12 (.split 11 17 (.split 11 18 (.split 12 13 (.split 12 16 (.split 13 14 (.split 13 18 (.split 14 15 (.split 15 18 (.split 14 17 (.split 14 18 (.split 17 18 (.split 14 16 (.split 16 17 (.split 15 16 (.path ![1,2,3,7,16,18,5,6,15]) (.path ![0,1,2,3,4,5,18,16,15])) (.four 8 16 17 18)) (.four 5 16 14 18)) (.four 5 17 8 18)) (.four 5 18 8 14)) (.four 5 17 8 14)) (.four 5 15 6 18)) (.four 5 15 6 14)) (.four 4 18 5 13)) (.four 4 14 5 13)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 18 8 11)) (.four 2 17 8 11)) (.four 2 12 3 11)) (.four 1 18 8 10)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowS_1_0_5_0_1 : checked (singleCase true 0 5 false true) [] rowS_1_0_5_0_1=true := by decide

def rowS_1_0_5_1_0 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 18 (.split 9 16 (.split 10 11 (.split 10 17 (.split 11 12 (.split 11 17 (.split 12 13 (.split 12 16 (.split 13 14 (.split 13 18 (.split 14 15 (.split 14 18 (.split 15 18 (.split 14 17 (.split 17 18 (.split 14 16 (.split 15 16 (.split 13 16 (.path ![2,1,0,7,16,18,5,4,13]) (.path ![0,6,18,16,13,4,3,2,8])) (.four 6 16 15 18)) (.four 5 16 14 18)) (.four 5 17 8 18)) (.four 5 17 8 14)) (.four 5 15 6 18)) (.four 5 18 6 14)) (.four 5 15 6 14)) (.four 4 18 5 13)) (.four 4 14 5 13)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 17 8 11)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 16 7 9)) (.four 0 18 6 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowS_1_0_5_1_0 : checked (singleCase true 0 5 true false) [] rowS_1_0_5_1_0=true := by decide

def rowS_1_0_5_1_1 : Tree 19 := (.four 5 18 6 8)
theorem ok_rowS_1_0_5_1_1 : checked (singleCase true 0 5 true true) [] rowS_1_0_5_1_1=true := by decide

def rowS_1_0_6_0_1 : Tree 19 := (.four 5 18 6 8)
theorem ok_rowS_1_0_6_0_1 : checked (singleCase true 0 6 false true) [] rowS_1_0_6_0_1=true := by decide

def rowS_1_0_6_1_0 : Tree 19 := (.four 0 16 7 18)
theorem ok_rowS_1_0_6_1_0 : checked (singleCase true 0 6 true false) [] rowS_1_0_6_1_0=true := by decide

def rowS_1_0_6_1_1 : Tree 19 := (.four 0 8 1 18)
theorem ok_rowS_1_0_6_1_1 : checked (singleCase true 0 6 true true) [] rowS_1_0_6_1_1=true := by decide

def rowS_1_1_0_0_1 : Tree 19 := (.split 9 10 (.split 10 18 (.split 9 15 (.split 15 18 (.split 9 16 (.split 9 18 (.split 16 18 (.split 9 17 (.split 10 11 (.split 10 17 (.split 11 12 (.split 11 17 (.split 12 13 (.split 12 16 (.split 12 18 (.split 13 14 (.split 14 15 (.split 14 17 (.split 16 17 (.split 15 17 (.path ![4,3,2,8,17,18,0,6,15]) (.path ![1,2,3,4,5,6,15,17,18])) (.four 7 17 16 18)) (.four 5 17 8 14)) (.four 5 15 6 14)) (.four 4 14 5 13)) (.four 3 18 7 12)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 17 8 11)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 17 9 18)) (.four 0 16 7 18)) (.four 0 18 7 9)) (.four 0 16 7 9)) (.four 0 15 6 18)) (.four 0 15 6 9)) (.four 0 10 1 18)) (.four 0 10 1 9))
theorem ok_rowS_1_1_0_0_1 : checked (singleCase true 1 0 false true) [] rowS_1_1_0_0_1=true := by decide

def rowS_1_1_0_1_0 : Tree 19 := (.four 1 17 8 18)
theorem ok_rowS_1_1_0_1_0 : checked (singleCase true 1 0 true false) [] rowS_1_1_0_1_0=true := by decide

def rowS_1_1_0_1_1 : Tree 19 := (.four 0 18 1 7)
theorem ok_rowS_1_1_0_1_1 : checked (singleCase true 1 0 true true) [] rowS_1_1_0_1_1=true := by decide

def rowS_1_1_1_0_1 : Tree 19 := (.four 0 18 1 7)
theorem ok_rowS_1_1_1_0_1 : checked (singleCase true 1 1 false true) [] rowS_1_1_1_0_1=true := by decide

def rowS_1_1_1_1_0 : Tree 19 := (.four 1 2 8 18)
theorem ok_rowS_1_1_1_1_0 : checked (singleCase true 1 1 true false) [] rowS_1_1_1_1_0=true := by decide

def rowS_1_1_1_1_1 : Tree 19 := (.four 0 18 1 7)
theorem ok_rowS_1_1_1_1_1 : checked (singleCase true 1 1 true true) [] rowS_1_1_1_1_1=true := by decide

def rowS_1_1_2_0_1 : Tree 19 := (.four 2 7 3 18)
theorem ok_rowS_1_1_2_0_1 : checked (singleCase true 1 2 false true) [] rowS_1_1_2_0_1=true := by decide

def rowS_1_1_2_1_0 : Tree 19 := (.four 2 17 8 18)
theorem ok_rowS_1_1_2_1_0 : checked (singleCase true 1 2 true false) [] rowS_1_1_2_1_0=true := by decide

def rowS_1_1_2_1_1 : Tree 19 := (.four 2 7 3 18)
theorem ok_rowS_1_1_2_1_1 : checked (singleCase true 1 2 true true) [] rowS_1_1_2_1_1=true := by decide

def rowS_1_1_3_0_1 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 16 (.split 9 18 (.split 10 11 (.split 10 17 (.split 11 12 (.split 11 18 (.split 11 17 (.split 12 13 (.split 13 18 (.split 12 16 (.split 12 18 (.split 16 18 (.split 12 17 (.split 13 14 (.split 14 15 (.split 14 17 (.split 16 17 (.split 13 17 (.path ![6,0,1,8,17,18,3,4,13]) (.path ![2,1,0,6,5,4,13,17,18])) (.four 7 17 16 18)) (.four 5 17 8 14)) (.four 5 15 6 14)) (.four 4 14 5 13)) (.four 3 17 12 18)) (.four 3 16 7 18)) (.four 3 18 7 12)) (.four 3 16 7 12)) (.four 3 13 4 18)) (.four 3 13 4 12)) (.four 2 17 8 11)) (.four 2 18 3 11)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 18 7 9)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowS_1_1_3_0_1 : checked (singleCase true 1 3 false true) [] rowS_1_1_3_0_1=true := by decide

def rowS_1_1_3_1_0 : Tree 19 := (.split 9 10 (.split 9 15 (.split 9 16 (.split 10 11 (.split 10 17 (.split 11 12 (.split 11 18 (.split 11 17 (.split 12 13 (.split 12 18 (.split 13 18 (.split 12 16 (.split 16 18 (.split 12 17 (.split 13 14 (.split 14 18 (.split 13 17 (.split 14 15 (.split 14 17 (.split 12 14 (.split 9 18 (.split 10 18 (.split 15 18 (.split 9 17 (.split 9 12 (.path ![9,0,6,5,8,17,18,3,12]) (.split 9 14 (.path ![0,9,12,3,18,17,8,5,14]) (.split 14 16 (.path ![1,8,5,14,9,12,3,7,16]) (.split 16 17 (.path ![1,0,7,16,14,5,4,18,17]) (.path ![0,1,2,3,4,5,14,16,17]))))) (.split 9 14 (.path ![2,1,0,9,17,18,4,5,14]) (.path ![1,2,3,18,17,9,14,5,6]))) (.split 12 15 (.split 13 15 (.split 16 17 (.split 14 16 (.split 9 17 (.split 9 12 (.path ![9,0,6,5,8,17,18,3,12]) (.split 9 14 (.path ![0,9,12,3,18,17,8,5,14]) (.path ![1,8,5,14,9,12,3,7,16]))) (.split 9 14 (.path ![2,1,0,9,17,18,4,5,14]) (.path ![1,2,3,18,17,9,14,5,6]))) (.path ![1,0,7,16,14,5,4,18,17])) (.split 15 16 (.split 14 16 (.split 9 17 (.split 9 12 (.path ![9,0,6,5,8,17,18,3,12]) (.split 9 14 (.path ![0,9,12,3,18,17,8,5,14]) (.path ![1,8,5,14,9,12,3,7,16]))) (.split 9 14 (.path ![2,1,0,9,17,18,4,5,14]) (.path ![1,2,3,18,17,9,14,5,6]))) (.path ![0,1,2,3,4,5,14,16,17])) (.four 15 17 16 18))) (.four 4 15 13 18)) (.four 3 15 12 18))) (.split 10 12 (.split 10 13 (.split 15 18 (.split 16 17 (.split 14 16 (.split 9 17 (.split 9 12 (.path ![9,0,6,5,8,17,18,3,12]) (.split 9 14 (.path ![0,9,12,3,18,17,8,5,14]) (.path ![1,8,5,14,9,12,3,7,16]))) (.split 9 14 (.path ![2,1,0,9,17,18,4,5,14]) (.path ![1,2,3,18,17,9,14,5,6]))) (.path ![1,0,7,16,14,5,4,18,17])) (.split 10 16 (.split 14 16 (.split 9 17 (.split 9 12 (.path ![9,0,6,5,8,17,18,3,12]) (.split 9 14 (.path ![0,9,12,3,18,17,8,5,14]) (.path ![1,8,5,14,9,12,3,7,16]))) (.split 9 14 (.path ![2,1,0,9,17,18,4,5,14]) (.path ![1,2,3,18,17,9,14,5,6]))) (.path ![0,1,2,3,4,5,14,16,17])) (.four 10 17 16 18))) (.split 12 15 (.split 13 15 (.split 16 17 (.split 14 16 (.split 9 17 (.split 9 12 (.path ![9,0,6,5,8,17,18,3,12]) (.split 9 14 (.path ![0,9,12,3,18,17,8,5,14]) (.path ![1,8,5,14,9,12,3,7,16]))) (.split 9 14 (.path ![2,1,0,9,17,18,4,5,14]) (.path ![1,2,3,18,17,9,14,5,6]))) (.path ![1,0,7,16,14,5,4,18,17])) (.split 10 16 (.split 15 16 (.split 14 16 (.split 9 17 (.split 9 12 (.path ![9,0,6,5,8,17,18,3,12]) (.split 9 14 (.path ![0,9,12,3,18,17,8,5,14]) (.path ![1,8,5,14,9,12,3,7,16]))) (.split 9 14 (.path ![2,1,0,9,17,18,4,5,14]) (.path ![1,2,3,18,17,9,14,5,6]))) (.path ![0,1,2,3,4,5,14,16,17])) (.four 15 17 16 18)) (.four 10 17 16 18))) (.four 4 15 13 18)) (.four 3 15 12 18))) (.four 4 10 13 18)) (.four 3 10 12 18))) (.path ![2,8,5,4,18,9,0,7,16])) (.path ![1,0,6,5,14,12,3,18,17])) (.four 5 17 8 14)) (.four 5 15 6 14)) (.four 4 17 13 18)) (.four 4 14 5 18)) (.four 4 14 5 13)) (.four 3 17 12 18)) (.four 3 16 7 18)) (.four 3 16 7 12)) (.four 3 13 4 18)) (.four 3 18 4 12)) (.four 3 13 4 12)) (.four 2 17 8 11)) (.four 2 18 3 11)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 16 7 9)) (.four 0 15 6 9)) (.four 0 10 1 9))
theorem ok_rowS_1_1_3_1_0 : checked (singleCase true 1 3 true false) [] rowS_1_1_3_1_0=true := by decide

def rowS_1_1_3_1_1 : Tree 19 := (.four 3 18 4 7)
theorem ok_rowS_1_1_3_1_1 : checked (singleCase true 1 3 true true) [] rowS_1_1_3_1_1=true := by decide

def rowS_1_1_4_0_1 : Tree 19 := (.four 3 18 4 7)
theorem ok_rowS_1_1_4_0_1 : checked (singleCase true 1 4 false true) [] rowS_1_1_4_0_1=true := by decide

def rowS_1_1_4_1_0 : Tree 19 := (.four 5 17 8 18)
theorem ok_rowS_1_1_4_1_0 : checked (singleCase true 1 4 true false) [] rowS_1_1_4_1_0=true := by decide

def rowS_1_1_4_1_1 : Tree 19 := (.four 3 18 4 7)
theorem ok_rowS_1_1_4_1_1 : checked (singleCase true 1 4 true true) [] rowS_1_1_4_1_1=true := by decide

def rowS_1_1_5_0_1 : Tree 19 := (.four 5 17 8 18)
theorem ok_rowS_1_1_5_0_1 : checked (singleCase true 1 5 false true) [] rowS_1_1_5_0_1=true := by decide

def rowS_1_1_5_1_0 : Tree 19 := (.four 5 17 8 18)
theorem ok_rowS_1_1_5_1_0 : checked (singleCase true 1 5 true false) [] rowS_1_1_5_1_0=true := by decide

def rowS_1_1_5_1_1 : Tree 19 := (.four 0 18 6 7)
theorem ok_rowS_1_1_5_1_1 : checked (singleCase true 1 5 true true) [] rowS_1_1_5_1_1=true := by decide

def rowS_1_1_6_0_1 : Tree 19 := (.four 0 18 6 7)
theorem ok_rowS_1_1_6_0_1 : checked (singleCase true 1 6 false true) [] rowS_1_1_6_0_1=true := by decide

def rowS_1_1_6_1_0 : Tree 19 := (.split 9 10 (.split 10 18 (.split 9 15 (.split 9 18 (.split 15 18 (.split 9 16 (.split 16 18 (.split 9 17 (.split 10 11 (.split 10 17 (.split 11 12 (.split 11 17 (.split 12 13 (.split 12 16 (.split 13 14 (.split 14 15 (.split 14 18 (.split 14 17 (.split 15 17 (.split 13 18 (.split 11 18 (.split 12 18 (.split 9 13 (.split 13 17 (.path ![9,0,18,17,8,2,3,4,13]) (.split 13 15 (.path ![1,2,3,4,13,17,18,6,15]) (.split 12 17 (.split 12 14 (.split 12 15 (.path ![0,6,15,13,17,8,2,3,12]) (.path ![0,7,3,12,15,13,17,8,5])) (.path ![0,1,8,17,13,4,3,12,14])) (.split 12 15 (.split 12 14 (.path ![1,0,18,17,12,3,4,5,14]) (.split 16 17 (.split 11 14 (.split 11 13 (.split 11 15 (.path ![0,6,15,13,17,12,3,2,11]) (.path ![0,1,2,11,15,13,17,12,14])) (.path ![1,2,11,13,17,18,6,5,14])) (.split 11 13 (.path ![0,1,2,11,14,12,17,13,4]) (.split 11 15 (.path ![1,0,6,15,13,11,14,12,3]) (.path ![1,0,6,15,11,14,12,3,4])))) (.split 14 16 (.split 15 16 (.split 11 16 (.split 11 13 (.split 11 14 (.split 11 15 (.path ![0,6,15,13,17,12,3,2,11]) (.path ![0,1,2,11,15,13,17,12,14])) (.path ![0,1,2,11,14,12,17,13,4])) (.split 11 14 (.path ![1,2,11,13,17,18,6,5,14]) (.split 13 16 (.split 11 15 (.path ![1,0,6,15,13,11,14,12,3]) (.path ![1,0,6,15,11,14,12,3,4])) (.path ![1,8,5,14,11,13,16,7,3])))) (.path ![0,6,5,4,3,2,11,16,17])) (.four 13 16 15 17)) (.four 12 16 14 17)))) (.four 12 13 15 17))))) (.split 13 16 (.path ![2,8,5,4,13,9,0,7,16]) (.split 11 16 (.split 11 13 (.path ![0,7,16,13,4,5,8,2,11]) (.split 11 14 (.split 13 17 (.split 16 17 (.path ![0,18,17,8,2,3,4,13,16]) (.split 12 17 (.path ![0,1,8,17,16,13,4,3,12]) (.path ![0,1,8,17,12,3,4,13,11]))) (.path ![1,2,11,13,17,18,6,5,14])) (.split 9 14 (.split 14 16 (.path ![1,8,5,14,11,13,16,7,3]) (.four 11 16 13 14)) (.four 9 11 13 14)))) (.split 9 11 (.split 16 17 (.split 13 17 (.path ![0,18,17,8,2,3,4,13,16]) (.split 13 15 (.path ![1,2,3,4,13,17,18,6,15]) (.split 11 15 (.split 12 15 (.split 12 17 (.path ![0,6,15,13,17,8,2,3,12]) (.split 9 12 (.split 12 14 (.path ![1,0,18,17,12,3,4,5,14]) (.split 14 16 (.path ![1,0,6,5,14,12,17,13,16]) (.split 9 14 (.path ![0,9,13,16,14,12,3,2,8]) (.four 9 16 13 14)))) (.four 9 17 12 13))) (.split 9 12 (.split 12 17 (.path ![0,7,3,12,15,13,17,8,5]) (.four 12 13 15 17)) (.four 9 15 12 13))) (.four 11 13 15 16)))) (.path ![0,6,5,4,3,2,11,16,17])) (.four 9 16 11 13))))) (.split 9 12 (.split 12 15 (.split 9 13 (.split 13 17 (.path ![9,0,18,17,8,2,3,4,13]) (.split 13 15 (.path ![1,2,3,4,13,17,18,6,15]) (.split 12 17 (.path ![0,6,15,13,17,8,2,3,12]) (.split 16 17 (.split 11 14 (.split 11 13 (.split 11 15 (.path ![0,6,15,13,17,12,3,2,11]) (.path ![0,1,2,11,15,13,4,5,14])) (.path ![1,2,11,13,17,18,6,5,14])) (.split 12 14 (.path ![0,6,5,14,11,2,3,12,17]) (.split 11 13 (.path ![0,1,2,11,14,12,17,13,4]) (.split 11 15 (.path ![1,0,6,15,13,11,14,12,3]) (.path ![1,0,6,15,11,14,12,3,4]))))) (.split 15 16 (.split 11 16 (.split 11 13 (.split 13 16 (.split 11 14 (.split 11 15 (.path ![0,6,15,13,17,12,3,2,11]) (.path ![0,1,2,11,15,13,4,5,14])) (.path ![0,1,2,11,14,5,4,13,17])) (.path ![0,7,16,13,4,5,8,2,11])) (.split 11 14 (.path ![1,2,11,13,17,18,6,5,14]) (.split 12 14 (.path ![0,6,5,14,11,2,3,12,17]) (.split 14 16 (.split 13 16 (.split 11 15 (.path ![1,0,6,15,13,11,14,12,3]) (.path ![1,0,6,15,11,14,12,3,4])) (.path ![1,8,5,14,11,13,16,7,3])) (.four 12 16 14 17))))) (.path ![0,6,5,4,3,2,11,16,17])) (.four 13 16 15 17)))))) (.split 13 16 (.path ![2,8,5,4,13,9,0,7,16]) (.split 11 16 (.split 11 13 (.path ![0,7,16,13,4,5,8,2,11]) (.split 11 14 (.split 13 17 (.split 16 17 (.path ![0,18,17,8,2,3,4,13,16]) (.split 12 17 (.path ![0,1,8,17,16,13,4,3,12]) (.path ![0,1,8,17,12,3,4,13,11]))) (.path ![1,2,11,13,17,18,6,5,14])) (.split 9 14 (.split 14 16 (.path ![1,8,5,14,11,13,16,7,3]) (.four 11 16 13 14)) (.four 9 11 13 14)))) (.split 9 11 (.split 16 17 (.split 13 17 (.path ![0,18,17,8,2,3,4,13,16]) (.split 13 15 (.path ![1,2,3,4,13,17,18,6,15]) (.split 11 15 (.split 12 17 (.path ![0,6,15,13,17,8,2,3,12]) (.split 11 13 (.path ![0,6,15,13,17,12,3,2,11]) (.split 15 16 (.split 11 14 (.path ![1,2,11,13,17,18,6,5,14]) (.split 9 14 (.split 14 16 (.split 12 14 (.path ![1,8,5,14,11,16,7,3,12]) (.path ![1,0,6,5,14,12,17,13,16])) (.four 11 16 13 14)) (.four 9 11 13 14))) (.four 11 15 13 16)))) (.four 11 13 15 16)))) (.path ![0,6,5,4,3,2,11,16,17])) (.four 9 16 11 13))))) (.four 6 12 15 18)) (.four 0 12 9 18))) (.split 9 11 (.split 11 15 (.split 12 18 (.split 13 17 (.split 9 13 (.path ![9,0,18,17,8,2,3,4,13]) (.split 13 16 (.path ![2,8,5,4,13,9,0,7,16]) (.split 16 17 (.path ![0,18,17,8,2,3,4,13,16]) (.split 11 16 (.split 11 13 (.path ![0,7,16,13,4,5,8,2,11]) (.split 12 17 (.path ![0,1,8,17,16,13,4,3,12]) (.path ![0,1,8,17,12,3,4,13,11]))) (.four 11 17 16 18))))) (.split 11 13 (.split 11 14 (.split 13 15 (.path ![1,2,3,4,13,17,18,6,15]) (.split 16 17 (.split 12 17 (.split 12 14 (.split 12 15 (.path ![0,6,15,13,17,8,2,3,12]) (.path ![0,7,3,12,15,13,17,8,5])) (.path ![0,1,8,17,13,4,3,12,14])) (.split 12 15 (.path ![0,6,15,13,17,12,3,2,11]) (.four 12 13 15 17))) (.split 11 16 (.split 15 16 (.split 13 16 (.split 9 13 (.split 12 17 (.split 12 14 (.split 12 15 (.path ![0,6,15,13,17,8,2,3,12]) (.path ![0,7,3,12,15,13,17,8,5])) (.path ![0,1,8,17,13,4,3,12,14])) (.split 12 15 (.path ![0,6,15,13,17,12,3,2,11]) (.four 12 13 15 17))) (.path ![2,8,5,4,13,9,0,7,16])) (.path ![0,7,16,13,4,5,8,2,11])) (.four 13 16 15 17)) (.four 11 17 16 18)))) (.path ![0,1,2,11,14,5,4,13,17])) (.four 11 17 13 18))) (.split 9 12 (.split 12 15 (.split 13 17 (.split 9 13 (.path ![9,0,18,17,8,2,3,4,13]) (.split 13 16 (.path ![2,8,5,4,13,9,0,7,16]) (.split 16 17 (.path ![0,18,17,8,2,3,4,13,16]) (.split 11 16 (.split 11 13 (.path ![0,7,16,13,4,5,8,2,11]) (.split 12 17 (.path ![0,1,8,17,16,13,4,3,12]) (.path ![0,1,8,17,12,3,4,13,11]))) (.four 11 17 16 18))))) (.split 11 13 (.split 11 14 (.split 13 15 (.path ![1,2,3,4,13,17,18,6,15]) (.split 12 17 (.path ![0,6,15,13,17,8,2,3,12]) (.path ![0,6,15,13,17,12,3,2,11]))) (.path ![0,1,2,11,14,5,4,13,17])) (.four 11 17 13 18))) (.four 6 12 15 18)) (.four 0 12 9 18))) (.four 6 11 15 18)) (.four 0 11 9 18))) (.split 9 13 (.split 13 15 (.split 13 16 (.path ![2,8,5,4,13,18,0,7,16]) (.path ![1,8,5,6,18,13,16,7,3])) (.four 6 13 15 18)) (.four 0 13 9 18))) (.four 6 17 15 18)) (.four 5 17 8 14)) (.four 5 18 6 14)) (.four 5 15 6 14)) (.four 4 14 5 13)) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 17 8 11)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 17 9 18)) (.four 0 16 7 18)) (.four 0 16 7 9)) (.four 0 15 6 18)) (.four 0 18 6 9)) (.four 0 15 6 9)) (.four 0 10 1 18)) (.four 0 10 1 9))
theorem ok_rowS_1_1_6_1_0 : checked (singleCase true 1 6 true false) [] rowS_1_1_6_1_0=true := by decide

def rowS_1_1_6_1_1 : Tree 19 := (.four 0 18 6 7)
theorem ok_rowS_1_1_6_1_1 : checked (singleCase true 1 6 true true) [] rowS_1_1_6_1_1=true := by decide

theorem single_case_all_rows (m : Bool) (c : Fin 2) (i : Fin 7) (wide opp : Bool)
    (h : wide=true ∨ opp=true) : ∃ t : Tree 19,checked (singleCase m c i wide opp) [] t=true := by
  cases m <;> fin_cases c <;> fin_cases i <;> cases wide <;> cases opp
  · simp at h
  · exact ⟨rowS_0_0_0_0_1,ok_rowS_0_0_0_0_1⟩
  · exact ⟨rowS_0_0_0_1_0,ok_rowS_0_0_0_1_0⟩
  · exact ⟨rowS_0_0_0_1_1,ok_rowS_0_0_0_1_1⟩
  · simp at h
  · exact ⟨rowS_0_0_1_0_1,ok_rowS_0_0_1_0_1⟩
  · exact ⟨rowS_0_0_1_1_0,ok_rowS_0_0_1_1_0⟩
  · exact ⟨rowS_0_0_1_1_1,ok_rowS_0_0_1_1_1⟩
  · simp at h
  · exact ⟨rowS_0_0_2_0_1,ok_rowS_0_0_2_0_1⟩
  · exact ⟨rowS_0_0_2_1_0,ok_rowS_0_0_2_1_0⟩
  · exact ⟨rowS_0_0_2_1_1,ok_rowS_0_0_2_1_1⟩
  · simp at h
  · exact ⟨rowS_0_0_3_0_1,ok_rowS_0_0_3_0_1⟩
  · exact ⟨rowS_0_0_3_1_0,ok_rowS_0_0_3_1_0⟩
  · exact ⟨rowS_0_0_3_1_1,ok_rowS_0_0_3_1_1⟩
  · simp at h
  · exact ⟨rowS_0_0_4_0_1,ok_rowS_0_0_4_0_1⟩
  · exact ⟨rowS_0_0_4_1_0,ok_rowS_0_0_4_1_0⟩
  · exact ⟨rowS_0_0_4_1_1,ok_rowS_0_0_4_1_1⟩
  · simp at h
  · exact ⟨rowS_0_0_5_0_1,ok_rowS_0_0_5_0_1⟩
  · exact ⟨rowS_0_0_5_1_0,ok_rowS_0_0_5_1_0⟩
  · exact ⟨rowS_0_0_5_1_1,ok_rowS_0_0_5_1_1⟩
  · simp at h
  · exact ⟨rowS_0_0_6_0_1,ok_rowS_0_0_6_0_1⟩
  · exact ⟨rowS_0_0_6_1_0,ok_rowS_0_0_6_1_0⟩
  · exact ⟨rowS_0_0_6_1_1,ok_rowS_0_0_6_1_1⟩
  · simp at h
  · exact ⟨rowS_0_1_0_0_1,ok_rowS_0_1_0_0_1⟩
  · exact ⟨rowS_0_1_0_1_0,ok_rowS_0_1_0_1_0⟩
  · exact ⟨rowS_0_1_0_1_1,ok_rowS_0_1_0_1_1⟩
  · simp at h
  · exact ⟨rowS_0_1_1_0_1,ok_rowS_0_1_1_0_1⟩
  · exact ⟨rowS_0_1_1_1_0,ok_rowS_0_1_1_1_0⟩
  · exact ⟨rowS_0_1_1_1_1,ok_rowS_0_1_1_1_1⟩
  · simp at h
  · exact ⟨rowS_0_1_2_0_1,ok_rowS_0_1_2_0_1⟩
  · exact ⟨rowS_0_1_2_1_0,ok_rowS_0_1_2_1_0⟩
  · exact ⟨rowS_0_1_2_1_1,ok_rowS_0_1_2_1_1⟩
  · simp at h
  · exact ⟨rowS_0_1_3_0_1,ok_rowS_0_1_3_0_1⟩
  · exact ⟨rowS_0_1_3_1_0,ok_rowS_0_1_3_1_0⟩
  · exact ⟨rowS_0_1_3_1_1,ok_rowS_0_1_3_1_1⟩
  · simp at h
  · exact ⟨rowS_0_1_4_0_1,ok_rowS_0_1_4_0_1⟩
  · exact ⟨rowS_0_1_4_1_0,ok_rowS_0_1_4_1_0⟩
  · exact ⟨rowS_0_1_4_1_1,ok_rowS_0_1_4_1_1⟩
  · simp at h
  · exact ⟨rowS_0_1_5_0_1,ok_rowS_0_1_5_0_1⟩
  · exact ⟨rowS_0_1_5_1_0,ok_rowS_0_1_5_1_0⟩
  · exact ⟨rowS_0_1_5_1_1,ok_rowS_0_1_5_1_1⟩
  · simp at h
  · exact ⟨rowS_0_1_6_0_1,ok_rowS_0_1_6_0_1⟩
  · exact ⟨rowS_0_1_6_1_0,ok_rowS_0_1_6_1_0⟩
  · exact ⟨rowS_0_1_6_1_1,ok_rowS_0_1_6_1_1⟩
  · simp at h
  · exact ⟨rowS_1_0_0_0_1,ok_rowS_1_0_0_0_1⟩
  · exact ⟨rowS_1_0_0_1_0,ok_rowS_1_0_0_1_0⟩
  · exact ⟨rowS_1_0_0_1_1,ok_rowS_1_0_0_1_1⟩
  · simp at h
  · exact ⟨rowS_1_0_1_0_1,ok_rowS_1_0_1_0_1⟩
  · exact ⟨rowS_1_0_1_1_0,ok_rowS_1_0_1_1_0⟩
  · exact ⟨rowS_1_0_1_1_1,ok_rowS_1_0_1_1_1⟩
  · simp at h
  · exact ⟨rowS_1_0_2_0_1,ok_rowS_1_0_2_0_1⟩
  · exact ⟨rowS_1_0_2_1_0,ok_rowS_1_0_2_1_0⟩
  · exact ⟨rowS_1_0_2_1_1,ok_rowS_1_0_2_1_1⟩
  · simp at h
  · exact ⟨rowS_1_0_3_0_1,ok_rowS_1_0_3_0_1⟩
  · exact ⟨rowS_1_0_3_1_0,ok_rowS_1_0_3_1_0⟩
  · exact ⟨rowS_1_0_3_1_1,ok_rowS_1_0_3_1_1⟩
  · simp at h
  · exact ⟨rowS_1_0_4_0_1,ok_rowS_1_0_4_0_1⟩
  · exact ⟨rowS_1_0_4_1_0,ok_rowS_1_0_4_1_0⟩
  · exact ⟨rowS_1_0_4_1_1,ok_rowS_1_0_4_1_1⟩
  · simp at h
  · exact ⟨rowS_1_0_5_0_1,ok_rowS_1_0_5_0_1⟩
  · exact ⟨rowS_1_0_5_1_0,ok_rowS_1_0_5_1_0⟩
  · exact ⟨rowS_1_0_5_1_1,ok_rowS_1_0_5_1_1⟩
  · simp at h
  · exact ⟨rowS_1_0_6_0_1,ok_rowS_1_0_6_0_1⟩
  · exact ⟨rowS_1_0_6_1_0,ok_rowS_1_0_6_1_0⟩
  · exact ⟨rowS_1_0_6_1_1,ok_rowS_1_0_6_1_1⟩
  · simp at h
  · exact ⟨rowS_1_1_0_0_1,ok_rowS_1_1_0_0_1⟩
  · exact ⟨rowS_1_1_0_1_0,ok_rowS_1_1_0_1_0⟩
  · exact ⟨rowS_1_1_0_1_1,ok_rowS_1_1_0_1_1⟩
  · simp at h
  · exact ⟨rowS_1_1_1_0_1,ok_rowS_1_1_1_0_1⟩
  · exact ⟨rowS_1_1_1_1_0,ok_rowS_1_1_1_1_0⟩
  · exact ⟨rowS_1_1_1_1_1,ok_rowS_1_1_1_1_1⟩
  · simp at h
  · exact ⟨rowS_1_1_2_0_1,ok_rowS_1_1_2_0_1⟩
  · exact ⟨rowS_1_1_2_1_0,ok_rowS_1_1_2_1_0⟩
  · exact ⟨rowS_1_1_2_1_1,ok_rowS_1_1_2_1_1⟩
  · simp at h
  · exact ⟨rowS_1_1_3_0_1,ok_rowS_1_1_3_0_1⟩
  · exact ⟨rowS_1_1_3_1_0,ok_rowS_1_1_3_1_0⟩
  · exact ⟨rowS_1_1_3_1_1,ok_rowS_1_1_3_1_1⟩
  · simp at h
  · exact ⟨rowS_1_1_4_0_1,ok_rowS_1_1_4_0_1⟩
  · exact ⟨rowS_1_1_4_1_0,ok_rowS_1_1_4_1_0⟩
  · exact ⟨rowS_1_1_4_1_1,ok_rowS_1_1_4_1_1⟩
  · simp at h
  · exact ⟨rowS_1_1_5_0_1,ok_rowS_1_1_5_0_1⟩
  · exact ⟨rowS_1_1_5_1_0,ok_rowS_1_1_5_1_0⟩
  · exact ⟨rowS_1_1_5_1_1,ok_rowS_1_1_5_1_1⟩
  · simp at h
  · exact ⟨rowS_1_1_6_0_1,ok_rowS_1_1_6_0_1⟩
  · exact ⟨rowS_1_1_6_1_0,ok_rowS_1_1_6_1_0⟩
  · exact ⟨rowS_1_1_6_1_1,ok_rowS_1_1_6_1_1⟩
#print axioms single_case_all_rows
end Graffiti133ExpandedPrivate
