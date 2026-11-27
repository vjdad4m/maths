import DisjointRotation31

namespace Graffiti384b.Disjoint30
open Finset SimpleGraph
open Graffiti384b.OneCommon (mark)
def price := 11111
def anchorAllowance := 100000
def row (i : ℕ) := if i≤0 then 1587222 else if i≤2 then 918918 else if i≤5 then 630630 else if i≤9 then 405405 else if i≤13 then 243243 else if i≤18 then 135135 else if i≤20 then 77778 else if i≤24 then 68607 else 66667

set_option maxRecDepth 65536 in
set_option maxHeartbeats 20000000 in
/-- The same incidence price is charged at each exterior vertex and
credited at the incident anchor. The three rows cover exterior vertices,
all anchors, and anchors that can fail in at least one trial. -/
theorem table :
    (∀ r : Fin 28,∀ b : Fin 22,∀ i j : Fin 4,
      mark r≤(b.val+(i.val+j.val)).choose 2 →
      (i.val+j.val≤2 → b.val+(i.val+j.val)≤10 → mark r≤RankTable.cap (b.val+(i.val+j.val)) 3) →
      rotation b 0 i j+price*(i.val+j.val)≤row r) ∧
    (∀ r : Fin 28,∀ b : Fin 23,mark r≤2+(b.val+5).choose 2 →
      anchorAllowance≤row r+price*b.val) ∧
    (∀ r : Fin 28,∀ b : Fin 23,∀ j : Fin 2,mark r≤1+(b.val+1+j.val).choose 2 →
      anchorAllowance+(3-2*j.val)*(22-b.val).choose 8≤row r+price*b.val) ∧
    (∑ r∈range 28,row r)=9217200 ∧ 9217200<6*anchorAllowance+27*(22:ℕ).choose 8 := by
  unfold mark row price anchorAllowance rotation weight bill FiniteRange.badCount RankTable.cap
  simp only [Nat.choose_eq_fast_choose]
  decide
end Graffiti384b.Disjoint30
#print axioms Graffiti384b.Disjoint30.table
