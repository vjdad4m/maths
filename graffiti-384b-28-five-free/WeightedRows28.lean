import SparseLink28

namespace Graffiti384b.Sparse28
open Finset HighSquare28

def price (i : ℕ) : ℕ :=
  [3472250,3472250,2693174,2056252,1983254,1393184,1346332,948090,948090,756262,756262,378235,
   378235,311168,311168,219076,170170,170170,170170,170170,118261,118261,118261,118261][i]?.getD 0

def mass (d p s : ℕ) := 6*bill 24 8 d p+4*bill 24 7 d (p+s)+bill 24 9 d s

set_option maxRecDepth 32768 in
set_option maxHeartbeats 10000000 in
theorem rows : ∀ i d : Fin 24,∀ p : Fin 3,∀ s : Fin 2,
    let z := d.val+p.val+s.val
    (i.val+2≤RankTable.cap z 3 ∨ 10≤z) →
    (mass d p s≤price i+636922) ∧
    ((p.val+s.val≤1 → z≤10 → i.val+2≤squareCap z) → mass d p s≤price i) := by
  unfold price mass bill FiniteRange.badCount RankTable.cap squareCap
  simp only [Nat.choose_eq_fast_choose]
  decide

theorem totals : (∑ i∈range 24,price i)=22577006 ∧
    22577006+6*636922 < 6*(4*(24:ℕ).choose 8)+4*(4*(24:ℕ).choose 7)+3*(24:ℕ).choose 9 := by decide

end Graffiti384b.Sparse28
#print axioms Graffiti384b.Sparse28.rows
#print axioms Graffiti384b.Sparse28.totals
