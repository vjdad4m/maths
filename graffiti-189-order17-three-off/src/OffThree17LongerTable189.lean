import OffThree17LongerRow2_5189
import OffThree17LongerRow2_6189
import OffThree17LongerRow2_7189
import OffThree17LongerRow2_8189
import OffThree17LongerRow2_9189
import OffThree17LongerRow2_10189
import OffThree17LongerRow2_11189
import OffThree17LongerRow3_6189
import OffThree17LongerRow3_7189
import OffThree17LongerRow3_8189
import OffThree17LongerRow3_9189
import OffThree17LongerRow3_10189
import OffThree17LongerRow4_7189
import OffThree17LongerRow4_8189
import OffThree17LongerRow4_9189
import OffThree17LongerRow5_8189
namespace OffThree17Longer

theorem all_rows (i j : ℕ) (lo : 1<i) (gap : i+3≤j) (orient : i+j≤13) (hi : j≤11) :
    row i j=true := by
  have e : i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases e with rfl|rfl|rfl|rfl
  · have e : j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 := by omega
    rcases e with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact row_2_5
    · exact row_2_6
    · exact row_2_7
    · exact row_2_8
    · exact row_2_9
    · exact row_2_10
    · exact row_2_11
  · have e : j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
    rcases e with rfl|rfl|rfl|rfl|rfl
    · exact row_3_6
    · exact row_3_7
    · exact row_3_8
    · exact row_3_9
    · exact row_3_10
  · have e : j=7 ∨ j=8 ∨ j=9 := by omega
    rcases e with rfl|rfl|rfl
    · exact row_4_7
    · exact row_4_8
    · exact row_4_9
  · have e : j=8 := by omega
    subst j
    exact row_5_8

#print axioms all_rows
end OffThree17Longer
