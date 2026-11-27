import NestedCorePrivateAdjacentSatSpec133
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Graffiti133NestedWeightedCore
open Graffiti133PrivateGeneric Graffiti133NestedActive
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
private def row_1_1_0 : Tree 22 := (.four 1 2 8 18)
private theorem test_1_1_0 : checked (satSpec true 1 0) [] row_1_1_0=true ∧ usesOnly (satActive 0) row_1_1_0=true := ⟨by decide, by decide⟩

private def row_1_1_1 : Tree 22 := (.four 1 2 8 18)
private theorem test_1_1_1 : checked (satSpec true 1 1) [] row_1_1_1=true ∧ usesOnly (satActive 1) row_1_1_1=true := ⟨by decide, by decide⟩

private def row_1_1_2 : Tree 22 := (.four 1 2 8 18)
private theorem test_1_1_2 : checked (satSpec true 1 2) [] row_1_1_2=true ∧ usesOnly (satActive 2) row_1_1_2=true := ⟨by decide, by decide⟩

private def row_1_1_3 : Tree 22 := (.four 1 2 8 18)
private theorem test_1_1_3 : checked (satSpec true 1 3) [] row_1_1_3=true ∧ usesOnly (satActive 3) row_1_1_3=true := ⟨by decide, by decide⟩

private def row_1_1_4 : Tree 22 := (.four 1 2 8 18)
private theorem test_1_1_4 : checked (satSpec true 1 4) [] row_1_1_4=true ∧ usesOnly (satActive 4) row_1_1_4=true := ⟨by decide, by decide⟩

private def row_1_1_5 : Tree 22 := (.four 1 2 8 18)
private theorem test_1_1_5 : checked (satSpec true 1 5) [] row_1_1_5=true ∧ usesOnly (satActive 5) row_1_1_5=true := ⟨by decide, by decide⟩

private def row_1_1_6 : Tree 22 := (.four 1 2 8 18)
private theorem test_1_1_6 : checked (satSpec true 1 6) [] row_1_1_6=true ∧ usesOnly (satActive 6) row_1_1_6=true := ⟨by decide, by decide⟩

private def row_1_1_7 : Tree 22 := (.four 1 2 8 18)
private theorem test_1_1_7 : checked (satSpec true 1 7) [] row_1_1_7=true ∧ usesOnly (satActive 7) row_1_1_7=true := ⟨by decide, by decide⟩

theorem satSuccess_1_1 (mask : Fin 8) : ∃ t,checked (satSpec true 1 mask) [] t=true ∧ usesOnly (satActive mask) t=true := by
  fin_cases mask
  · exact ⟨_,test_1_1_0⟩
  · exact ⟨_,test_1_1_1⟩
  · exact ⟨_,test_1_1_2⟩
  · exact ⟨_,test_1_1_3⟩
  · exact ⟨_,test_1_1_4⟩
  · exact ⟨_,test_1_1_5⟩
  · exact ⟨_,test_1_1_6⟩
  · exact ⟨_,test_1_1_7⟩

#print axioms satSuccess_1_1
end Graffiti133NestedWeightedCore
