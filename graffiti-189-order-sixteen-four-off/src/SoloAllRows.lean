import Solo_row_1_4
import Solo_row_1_5
import Solo_row_1_6
import Solo_row_1_7
import Solo_row_1_8
import Solo_row_1_9
import Solo_row_1_10
import Solo_row_2_5
import Solo_row_2_6
import Solo_row_2_7
import Solo_row_2_8
import Solo_row_2_9
import Solo_row_3_6
import Solo_row_3_7
import Solo_row_3_8
import Solo_row_4_7
namespace OffFour16Solo

private theorem row_transport {i j a b : ℕ} (hi : i=a) (hj : j=b)
    (h : row a b=true) : row i j=true :=
  Eq.mpr (congrArg (fun q => q=true) (congrArg₂ row hi hj)) h
theorem all_rows (i j : ℕ) (ip : 1≤i) (gap : i+3≤j) (oriented : i≤11-j) (jr : j≤10) :
    row i j=true := by
  have p : i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases p with a|a|a|a
  · have hj : j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
    rcases hj with b|b|b|b|b|b|b
    · exact @row_transport i j 1 4 a b row_1_4
    · exact @row_transport i j 1 5 a b row_1_5
    · exact @row_transport i j 1 6 a b row_1_6
    · exact @row_transport i j 1 7 a b row_1_7
    · exact @row_transport i j 1 8 a b row_1_8
    · exact @row_transport i j 1 9 a b row_1_9
    · exact @row_transport i j 1 10 a b row_1_10
  · have hj : j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
    rcases hj with b|b|b|b|b
    · exact @row_transport i j 2 5 a b row_2_5
    · exact @row_transport i j 2 6 a b row_2_6
    · exact @row_transport i j 2 7 a b row_2_7
    · exact @row_transport i j 2 8 a b row_2_8
    · exact @row_transport i j 2 9 a b row_2_9
  · have hj : j=6 ∨ j=7 ∨ j=8 := by omega
    rcases hj with b|b|b
    · exact @row_transport i j 3 6 a b row_3_6
    · exact @row_transport i j 3 7 a b row_3_7
    · exact @row_transport i j 3 8 a b row_3_8
  · have hj : j=7 := by omega
    exact @row_transport i j 4 7 a hj row_4_7
#print axioms all_rows

end OffFour16Solo
