import OffFive17SingletonRow5189
import OffFive17SingletonRow6189
import OffFive17SingletonRow8189
import OffFive17SingletonRow9189
import OffFive17SingletonRow10189
namespace OffFive17Singleton

theorem all_rows (j : ℕ) (lo : 4 ≤ j) (hi : j ≤ 10) (no4 : j≠4) (no7 : j≠7) :
    row j=true := by
  have h : j=5 ∨ j=6 ∨ j=8 ∨ j=9 ∨ j=10 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl
  · exact row_5
  · exact row_6
  · exact row_8
  · exact row_9
  · exact row_10

#print axioms all_rows
end OffFive17Singleton
