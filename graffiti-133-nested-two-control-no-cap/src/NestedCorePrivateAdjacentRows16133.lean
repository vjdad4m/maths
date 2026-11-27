import NestedCorePrivateAdjacentSatSpec133
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Graffiti133NestedWeightedCore
open Graffiti133PrivateGeneric Graffiti133NestedActive
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
private def row_1_6_0 : Tree 22 := (.split 8 18 (.split 7 18 (.split 7 19 (.split 7 21 (.split 9 10 (.split 10 18 (.split 9 15 (.split 9 18 (.split 15 18 (.split 9 16 (.split 16 18 (.split 7 20 (.split 9 19 (.split 9 20 (.split 9 21 (.split 8 19 (.split 10 11 (.split 10 19 (.split 10 17 (.split 8 20 (.split 11 12 (.split 11 20 (.split 12 19 (.split 19 20 (.split 11 17 (.split 17 19 (.split 11 18 (.split 12 13 (.split 12 21 (.split 13 20 (.split 20 21 (.split 12 16 (.split 16 20 (.path ![1,8,5,6,18,20,3,7,16]) (.four 3 16 7 20)) (.four 3 16 7 12)) (.four 3 21 4 20)) (.four 3 13 4 20)) (.four 3 21 4 12)) (.four 3 13 4 12)) (.four 2 18 11 19)) (.four 2 17 8 19)) (.four 2 17 8 11)) (.four 2 20 3 19)) (.four 2 12 3 19)) (.four 2 20 3 11)) (.four 2 12 3 11)) (.four 2 20 3 8)) (.four 1 17 8 10)) (.four 1 19 2 10)) (.four 1 11 2 10)) (.four 1 19 2 8)) (.four 0 21 9 18)) (.four 0 20 9 18)) (.four 0 19 9 18)) (.four 0 20 7 18)) (.four 0 16 7 18)) (.four 0 16 7 9)) (.four 0 15 6 18)) (.four 0 18 6 9)) (.four 0 15 6 9)) (.four 0 10 1 18)) (.four 0 10 1 9)) (.four 0 21 7 18)) (.four 0 19 7 18)) (.four 0 18 6 7)) (.four 0 8 1 18))
private theorem test_1_6_0 : checked (satSpec true 6 0) [] row_1_6_0=true ∧ usesOnly (satActive 0) row_1_6_0=true := ⟨by decide, by decide⟩

private def row_1_6_1 : Tree 22 := (.split 8 18 (.split 7 18 (.split 7 21 (.split 9 10 (.split 10 18 (.split 9 15 (.split 9 18 (.split 15 18 (.split 9 16 (.split 16 18 (.split 7 20 (.split 9 11 (.split 9 20 (.split 9 21 (.split 10 11 (.split 10 17 (.split 8 20 (.split 11 12 (.split 11 20 (.split 11 17 (.split 12 13 (.split 12 21 (.split 13 20 (.split 20 21 (.split 12 16 (.split 16 20 (.path ![1,8,5,6,18,20,3,7,16]) (.four 3 16 7 20)) (.four 3 16 7 12)) (.four 3 21 4 20)) (.four 3 13 4 20)) (.four 3 21 4 12)) (.four 3 13 4 12)) (.four 2 17 8 11)) (.four 2 20 3 11)) (.four 2 12 3 11)) (.four 2 20 3 8)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 21 9 18)) (.four 0 20 9 18)) (.four 0 11 9 18)) (.four 0 20 7 18)) (.four 0 16 7 18)) (.four 0 16 7 9)) (.four 0 15 6 18)) (.four 0 18 6 9)) (.four 0 15 6 9)) (.four 0 10 1 18)) (.four 0 10 1 9)) (.four 0 21 7 18)) (.four 0 18 6 7)) (.four 0 8 1 18))
private theorem test_1_6_1 : checked (satSpec true 6 1) [] row_1_6_1=true ∧ usesOnly (satActive 1) row_1_6_1=true := ⟨by decide, by decide⟩

private def row_1_6_2 : Tree 22 := (.split 8 18 (.split 7 18 (.split 7 19 (.split 7 21 (.split 9 10 (.split 10 18 (.split 9 15 (.split 9 18 (.split 15 18 (.split 9 16 (.split 16 18 (.split 9 12 (.split 9 19 (.split 9 21 (.split 8 19 (.split 10 11 (.split 10 19 (.split 10 17 (.split 11 12 (.split 12 19 (.split 11 17 (.split 17 19 (.split 11 18 (.split 12 13 (.split 12 21 (.split 12 16 (.path ![1,8,5,6,18,12,3,7,16]) (.four 3 16 7 12)) (.four 3 21 4 12)) (.four 3 13 4 12)) (.four 2 18 11 19)) (.four 2 17 8 19)) (.four 2 17 8 11)) (.four 2 12 3 19)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 19 2 10)) (.four 1 11 2 10)) (.four 1 19 2 8)) (.four 0 21 9 18)) (.four 0 19 9 18)) (.four 0 12 9 18)) (.four 0 16 7 18)) (.four 0 16 7 9)) (.four 0 15 6 18)) (.four 0 18 6 9)) (.four 0 15 6 9)) (.four 0 10 1 18)) (.four 0 10 1 9)) (.four 0 21 7 18)) (.four 0 19 7 18)) (.four 0 18 6 7)) (.four 0 8 1 18))
private theorem test_1_6_2 : checked (satSpec true 6 2) [] row_1_6_2=true ∧ usesOnly (satActive 2) row_1_6_2=true := ⟨by decide, by decide⟩

private def row_1_6_3 : Tree 22 := (.split 8 18 (.split 7 18 (.split 7 21 (.split 9 10 (.split 10 18 (.split 9 15 (.split 9 18 (.split 15 18 (.split 9 16 (.split 16 18 (.split 9 11 (.split 9 12 (.split 9 21 (.split 10 11 (.split 10 17 (.split 11 12 (.split 11 17 (.split 12 13 (.split 12 21 (.split 12 16 (.path ![1,8,5,6,18,12,3,7,16]) (.four 3 16 7 12)) (.four 3 21 4 12)) (.four 3 13 4 12)) (.four 2 17 8 11)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 21 9 18)) (.four 0 12 9 18)) (.four 0 11 9 18)) (.four 0 16 7 18)) (.four 0 16 7 9)) (.four 0 15 6 18)) (.four 0 18 6 9)) (.four 0 15 6 9)) (.four 0 10 1 18)) (.four 0 10 1 9)) (.four 0 21 7 18)) (.four 0 18 6 7)) (.four 0 8 1 18))
private theorem test_1_6_3 : checked (satSpec true 6 3) [] row_1_6_3=true ∧ usesOnly (satActive 3) row_1_6_3=true := ⟨by decide, by decide⟩

private def row_1_6_4 : Tree 22 := (.split 8 18 (.split 7 18 (.split 7 19 (.split 9 10 (.split 10 18 (.split 9 15 (.split 9 18 (.split 15 18 (.split 9 16 (.split 16 18 (.split 7 20 (.split 9 13 (.split 9 19 (.split 9 20 (.split 8 19 (.split 10 11 (.split 10 19 (.split 10 17 (.split 8 20 (.split 11 12 (.split 11 20 (.split 12 19 (.split 19 20 (.split 11 17 (.split 17 19 (.split 11 18 (.split 12 13 (.split 13 20 (.split 12 16 (.split 16 20 (.path ![1,8,5,6,18,20,3,7,16]) (.four 3 16 7 20)) (.four 3 16 7 12)) (.four 3 13 4 20)) (.four 3 13 4 12)) (.four 2 18 11 19)) (.four 2 17 8 19)) (.four 2 17 8 11)) (.four 2 20 3 19)) (.four 2 12 3 19)) (.four 2 20 3 11)) (.four 2 12 3 11)) (.four 2 20 3 8)) (.four 1 17 8 10)) (.four 1 19 2 10)) (.four 1 11 2 10)) (.four 1 19 2 8)) (.four 0 20 9 18)) (.four 0 19 9 18)) (.four 0 13 9 18)) (.four 0 20 7 18)) (.four 0 16 7 18)) (.four 0 16 7 9)) (.four 0 15 6 18)) (.four 0 18 6 9)) (.four 0 15 6 9)) (.four 0 10 1 18)) (.four 0 10 1 9)) (.four 0 19 7 18)) (.four 0 18 6 7)) (.four 0 8 1 18))
private theorem test_1_6_4 : checked (satSpec true 6 4) [] row_1_6_4=true ∧ usesOnly (satActive 4) row_1_6_4=true := ⟨by decide, by decide⟩

private def row_1_6_5 : Tree 22 := (.split 8 18 (.split 7 18 (.split 9 10 (.split 10 18 (.split 9 15 (.split 9 18 (.split 15 18 (.split 9 16 (.split 16 18 (.split 7 20 (.split 9 11 (.split 9 13 (.split 9 20 (.split 10 11 (.split 10 17 (.split 8 20 (.split 11 12 (.split 11 20 (.split 11 17 (.split 12 13 (.split 13 20 (.split 12 16 (.split 16 20 (.path ![1,8,5,6,18,20,3,7,16]) (.four 3 16 7 20)) (.four 3 16 7 12)) (.four 3 13 4 20)) (.four 3 13 4 12)) (.four 2 17 8 11)) (.four 2 20 3 11)) (.four 2 12 3 11)) (.four 2 20 3 8)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 20 9 18)) (.four 0 13 9 18)) (.four 0 11 9 18)) (.four 0 20 7 18)) (.four 0 16 7 18)) (.four 0 16 7 9)) (.four 0 15 6 18)) (.four 0 18 6 9)) (.four 0 15 6 9)) (.four 0 10 1 18)) (.four 0 10 1 9)) (.four 0 18 6 7)) (.four 0 8 1 18))
private theorem test_1_6_5 : checked (satSpec true 6 5) [] row_1_6_5=true ∧ usesOnly (satActive 5) row_1_6_5=true := ⟨by decide, by decide⟩

private def row_1_6_6 : Tree 22 := (.split 8 18 (.split 7 18 (.split 7 19 (.split 9 10 (.split 10 18 (.split 9 15 (.split 9 18 (.split 15 18 (.split 9 16 (.split 16 18 (.split 9 12 (.split 9 13 (.split 9 19 (.split 8 19 (.split 10 11 (.split 10 19 (.split 10 17 (.split 11 12 (.split 12 19 (.split 11 17 (.split 17 19 (.split 11 18 (.split 12 13 (.split 12 16 (.path ![1,8,5,6,18,12,3,7,16]) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 18 11 19)) (.four 2 17 8 19)) (.four 2 17 8 11)) (.four 2 12 3 19)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 19 2 10)) (.four 1 11 2 10)) (.four 1 19 2 8)) (.four 0 19 9 18)) (.four 0 13 9 18)) (.four 0 12 9 18)) (.four 0 16 7 18)) (.four 0 16 7 9)) (.four 0 15 6 18)) (.four 0 18 6 9)) (.four 0 15 6 9)) (.four 0 10 1 18)) (.four 0 10 1 9)) (.four 0 19 7 18)) (.four 0 18 6 7)) (.four 0 8 1 18))
private theorem test_1_6_6 : checked (satSpec true 6 6) [] row_1_6_6=true ∧ usesOnly (satActive 6) row_1_6_6=true := ⟨by decide, by decide⟩

private def row_1_6_7 : Tree 22 := (.split 8 18 (.split 7 18 (.split 9 10 (.split 10 18 (.split 9 15 (.split 9 18 (.split 15 18 (.split 9 16 (.split 16 18 (.split 9 11 (.split 9 12 (.split 9 13 (.split 10 11 (.split 10 17 (.split 11 12 (.split 11 17 (.split 12 13 (.split 12 16 (.path ![1,8,5,6,18,12,3,7,16]) (.four 3 16 7 12)) (.four 3 13 4 12)) (.four 2 17 8 11)) (.four 2 12 3 11)) (.four 1 17 8 10)) (.four 1 11 2 10)) (.four 0 13 9 18)) (.four 0 12 9 18)) (.four 0 11 9 18)) (.four 0 16 7 18)) (.four 0 16 7 9)) (.four 0 15 6 18)) (.four 0 18 6 9)) (.four 0 15 6 9)) (.four 0 10 1 18)) (.four 0 10 1 9)) (.four 0 18 6 7)) (.four 0 8 1 18))
private theorem test_1_6_7 : checked (satSpec true 6 7) [] row_1_6_7=true ∧ usesOnly (satActive 7) row_1_6_7=true := ⟨by decide, by decide⟩

theorem satSuccess_1_6 (mask : Fin 8) : ∃ t,checked (satSpec true 6 mask) [] t=true ∧ usesOnly (satActive mask) t=true := by
  fin_cases mask
  · exact ⟨_,test_1_6_0⟩
  · exact ⟨_,test_1_6_1⟩
  · exact ⟨_,test_1_6_2⟩
  · exact ⟨_,test_1_6_3⟩
  · exact ⟨_,test_1_6_4⟩
  · exact ⟨_,test_1_6_5⟩
  · exact ⟨_,test_1_6_6⟩
  · exact ⟨_,test_1_6_7⟩

#print axioms satSuccess_1_6
end Graffiti133NestedWeightedCore
