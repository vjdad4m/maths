import OffFour17Row3_3_6189
import OffFour17Row3_3_7189
import OffFour17Row3_3_8189
import OffFour17Row3_3_9189
import OffFour17Row3_4_7189
import OffFour17Row3_4_8189
namespace OffFour17
theorem disc_row (i j : ℕ)
    (lo : 3 ≤ i) (hi : j ≤ 9) (gap : i+3 ≤ j) (mode : i+j ≤ 12) :
    row 3 i j=true := by
  have e : i=3 ∨ i=4 := by omega
  rcases e with rfl|rfl
  · have h : j=6 ∨ j=7 ∨ j=8 ∨ j=9 := by omega
    rcases h with rfl|rfl|rfl|rfl
    · exact row_3_3_6
    · exact row_3_3_7
    · exact row_3_3_8
    · exact row_3_3_9
  · have h : j=7 ∨ j=8 := by omega
    rcases h with rfl|rfl
    · exact row_3_4_7
    · exact row_3_4_8

#print axioms disc_row
end OffFour17
