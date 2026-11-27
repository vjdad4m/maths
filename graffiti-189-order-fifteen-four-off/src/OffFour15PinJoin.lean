import OffFour15RowGroup1
import OffFour15RowGroup2
import OffFour15RowGroup3
import OffFour15RowGroup4
namespace OffFour15

private theorem row_transport {i j a b : ℕ} (hi : i=a) (hj : j=b)
    (h : row a b=true) : row i j=true :=
  Eq.mpr (congrArg (fun q => q=true) (congrArg₂ row hi hj)) h

theorem all_rows (i j : ℕ) (il : 1≤i) (ij : i+3≤j) (jr : j≤9) : row i j=true := by
  have hi : i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
  rcases hi with a|a|a|a|a|a
  · have hj : j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
    rcases hj with b|b|b|b|b|b
    · exact @row_transport i j 1 4 a b row_1_4
    · exact @row_transport i j 1 5 a b row_1_5
    · exact @row_transport i j 1 6 a b row_1_6
    · exact @row_transport i j 1 7 a b row_1_7
    · exact @row_transport i j 1 8 a b row_1_8
    · exact @row_transport i j 1 9 a b row_1_9
  · have hj : j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
    rcases hj with b|b|b|b|b
    · exact @row_transport i j 2 5 a b row_2_5
    · exact @row_transport i j 2 6 a b row_2_6
    · exact @row_transport i j 2 7 a b row_2_7
    · exact @row_transport i j 2 8 a b row_2_8
    · exact @row_transport i j 2 9 a b row_2_9
  · have hj : j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
    rcases hj with b|b|b|b
    · exact @row_transport i j 3 6 a b row_3_6
    · exact @row_transport i j 3 7 a b row_3_7
    · exact @row_transport i j 3 8 a b row_3_8
    · exact @row_transport i j 3 9 a b row_3_9
  · have hj : j=7 ∨ j=8 ∨ j=9 := by omega
    rcases hj with b|b|b
    · exact @row_transport i j 4 7 a b row_4_7
    · exact @row_transport i j 4 8 a b row_4_8
    · exact @row_transport i j 4 9 a b row_4_9
  · have hj : j=8 ∨ j=9 := by omega
    rcases hj with b|b
    · exact @row_transport i j 5 8 a b row_5_8
    · exact @row_transport i j 5 9 a b row_5_9
  · have b : j=9 := by omega
    exact @row_transport i j 6 9 a b row_6_9

#print axioms all_rows
end OffFour15
