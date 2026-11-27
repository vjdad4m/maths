import SquareResidual28

namespace Graffiti384b.HighSquare28
open Finset SimpleGraph

def pairedPrice (i : ℕ) : ℕ :=
  [1091740,789412,789412,534820,534820,534820,340340,340340,340340,340340,203060,203060,
   203060,203060,112970,112970,112970,112970,112970,61490,61490,61490,61490,61490][i]?.getD 0

def residualPrice (i : ℕ) : ℕ := if i≤1 then 2164746 else Thin28.price i

def fee (a : ℕ) : ℕ := if a=2 then 1430680 else 1605170

set_option maxRecDepth 32768 in
theorem paired_rows : ∀ i : Fin 24, ∀ a : Fin 24, ∀ x y : Fin 2,
    let d := a.val+x.val+y.val
    (i.val+3≤RankTable.cap d 3 ∨ 10≤d) →
    (if x.val=0 then FiniteRange.badCount 24 9 a else (23-a.val).choose 9) +
    (if y.val=0 then FiniteRange.badCount 24 9 a else (23-a.val).choose 9) ≤ pairedPrice i := by
  unfold pairedPrice RankTable.cap FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide

set_option maxRecDepth 32768 in
theorem single_rows : ∀ i : Fin 27, ∀ a : Fin 25, ∀ c : Fin 3,
    let d := a.val+c.val
    (i.val+2≤RankTable.cap d 3 ∨ 10≤d) →
    (c.val=2 → 5≤d) →
    3*(if c.val=0 then FiniteRange.badCount 25 8 a else if c.val=1 then (24-a.val).choose 8 else 0)
      +FiniteRange.badCount 25 10 a+205000*c.val ≤ residualPrice i +
        (if d=3 then 726750 else 0)+(if c.val=2 then 292516 else 0) := by
  unfold residualPrice Thin28.price RankTable.cap FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide

set_option maxRecDepth 32768 in
theorem end_rows : ∀ i : Fin 27, ∀ a : Fin 26, 2≤a.val → i.val+2≤2+a.val.choose 2 →
    (25-a.val).choose 10+fee a ≤ residualPrice i+205000*a.val := by
  unfold residualPrice Thin28.price fee
  simp only [Nat.choose_eq_fast_choose]
  decide

theorem totals : (∑ i∈range 24,pairedPrice i)=7320924 ∧
    (∑ i∈range 27,residualPrice i)=24783751 := by decide

end Graffiti384b.HighSquare28
#print axioms Graffiti384b.HighSquare28.paired_rows
#print axioms Graffiti384b.HighSquare28.single_rows
#print axioms Graffiti384b.HighSquare28.end_rows
#print axioms Graffiti384b.HighSquare28.totals
