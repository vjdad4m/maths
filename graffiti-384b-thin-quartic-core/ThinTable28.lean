import FourFrontier28

namespace Graffiti384b.Thin28
open Finset

def price (i : ℕ) : ℕ :=
  [2891496,2891496,2164746,2164746,1536834,1536834,1536834,1039584,1039584,1039584,1039584,
   671752,671752,671752,671752,467548,467548,467548,467548,467548,343138,343138,343138,343138,
   343138,343138,272353][i]?.getD 0

set_option maxRecDepth 32768 in
theorem exterior_rows : ∀ i : Fin 27, ∀ d : Fin 26,
    (i.val+2 ≤ RankTable.cap d 3 ∨ 10≤d.val) →
    (3*FiniteRange.badCount 25 8 d+FiniteRange.badCount 25 10 d≤price i) ∧
    (0<d.val → 3*(25-d.val).choose 8+FiniteRange.badCount 25 10 (d.val-1)+205000≤price i) := by
  unfold price RankTable.cap FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide

set_option maxRecDepth 32768 in
theorem endpoint_rows : ∀ i : Fin 27, ∀ a : Fin 26, i.val+2 ≤ 1+a.val.choose 2 →
    (25-a.val).choose 10+1734380 ≤ price i+205000*a.val := by
  unfold price
  simp only [Nat.choose_eq_fast_choose]
  decide

theorem total_price : (∑ i∈range 27,price i)=26237251 := by decide

end Graffiti384b.Thin28
#print axioms Graffiti384b.Thin28.exterior_rows
#print axioms Graffiti384b.Thin28.endpoint_rows
#print axioms Graffiti384b.Thin28.total_price
