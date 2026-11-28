import SimplicialCredit30
import BoundaryFiber384b

namespace Graffiti384b.Types28
open Finset SimpleGraph Thin28 EarMix
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private CliqueChoice.degree_neighbor from CliqueChoice384b
open private Repair.triangles_le_choose from Repair384b

def row (r : ℕ) : ℕ := [2138906,1552661,1528436,1528436,1024556,1024556,1024556,1024556,
  646646,646646,646646,646646,646646,384098,384098,384098,384098,384098,384098,
  213928,213928,213928,213928,213928,213928,213928][r]?.getD 0

set_option maxRecDepth 32768 in
theorem rows : (∀ r : Fin 26,∀ d : Fin 12,3≤d.val → r.val+2≤d.val.choose 2 →
    (r.val+2<d.val.choose 2 → FiniteRange.badCount 26 10 d≤row r) ∧
    FiniteRange.badCount 26 10 d+min ((25:ℕ).choose 9) (FiniteRange.badCount 26 9 d)≤row r+(25:ℕ).choose 9 ∧
    (r.val+2<d.val.choose 2 → (26-d.val).choose 10+170170≤row r)) ∧
    (∑i∈range 26,row i)=17881977 := by
  unfold row FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem misses_bad (H k : Finset V) : misses G Hᶜ k=FiniteRange.bad G H k := by
  ext w; simp [misses,FiniteRange.bad,not_or,and_assoc]

theorem high_cost {H : Finset V} (sz : H.card=26) {v : V} (vh : v∈H) (dv : 3≤G.degree v)
    (r : ℕ) (rr : r<26) (lo : r+2≤trianglesAt G v) :
    hit G H Hᶜ 10 v≤row r+gain G H Hᶜ 10 v ∧
    ((∃e∉H,G.Adj v e ∧ G.degree e≤2) → hit G H Hᶜ 10 v+170170≤row r) := by
  classical
  let d := min (G.degree v) 11
  have small : d≤11 := min_le_right .. 
  have le : d≤G.degree v := min_le_left ..
  have floor : 3≤d := le_min dv (by decide)
  have cap := Repair.triangles_le_choose G v
  have bound : r+2≤d.choose 2 := by
    by_cases low : G.degree v≤11
    · simpa [d,min_eq_left low] using lo.trans cap
    · rw [show d=11 from min_eq_right (by omega)]
      change r+2≤55; omega
  have exactAt (eq : r+2=d.choose 2) : trianglesAt G v=(G.degree v).choose 2 := by
    have full : d=G.degree v := by
      by_contra ne
      have hi : d=11 := by dsimp [d] at *; omega
      rw [hi] at eq; change r+2=55 at eq; omega
    rw [full] at eq; omega
  obtain ⟨base,credit,edge⟩ := rows.1 ⟨r,rr⟩ ⟨d,Nat.lt_succ_of_le small⟩ floor bound
  have count (b : ℕ) : hit G H Hᶜ b v≤FiniteRange.badCount 26 b d := by
    simpa only [hit,misses_bad,sz] using FiniteRange.count_bad G H b d v vh le (by omega)
  constructor
  · have ten := count 10
    by_cases eq : r+2=d.choose 2
    · have a := active_fiber G vh (fun h => mem_compl.mp h vh) (exactAt eq) 9
      rw [sz] at a
      change (25:ℕ).choose 9≤gain G H Hᶜ 10 v+hit G H Hᶜ 9 v at a
      change FiniteRange.badCount 26 10 d+min ((25:ℕ).choose 9) (FiniteRange.badCount 26 9 d)≤row r+(25:ℕ).choose 9 at credit
      have nine := count 9; omega
    · have up := base (lt_of_le_of_ne bound eq)
      change FiniteRange.badCount 26 10 d≤row r at up; omega
  · rintro ⟨e,eh,ve,ed⟩
    have strict : r+2<d.choose 2 := lt_of_le_of_ne bound (fun eq => by
      have hd := CliqueChoice.degree_neighbor G (CliqueChoice.saturated_clique G (exactAt eq)) ve
      omega)
    have refund := edge strict
    have actual := BoundaryFiber.count G H 10 d vh eh ve le (by omega)
    change (26-d).choose 10+170170≤row r at refund
    unfold hit; simp_rw [misses_bad]; rw [sz] at actual
    omega
end Graffiti384b.Types28
#print axioms Graffiti384b.Types28.rows
#print axioms Graffiti384b.Types28.high_cost
