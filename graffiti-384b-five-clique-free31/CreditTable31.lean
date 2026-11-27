import CreditRanks31
namespace Graffiti384b.EarCredit.Pair
open Finset
def price (mode : ℕ) := if mode=0 then 308000 else if mode=1 then 306000 else 122000
def penalty (mode : ℕ) := if mode=1 then 260000 else 0
def rebate (mode j : ℕ) := if j=2 then penalty mode else 0
def minimumScore (mode i : ℕ) := if mode ≠ 0 ∧ i ≥ 3 then i+3 else i+2
def loss (d j : ℕ) := if j=0 then FiniteRange.badCount 27 9 d else if j=1 then (27-d).choose 9 else 0
def budget (mode i : ℕ) :=
  let s := minimumScore mode i
  max (loss (deg s) 0) (max (loss (if s≤3 then 3 else deg s) 1 + price mode)
    (if mode=0 then 0 else 2*price mode-penalty mode))
def pivotBill (mode : ℕ) := if mode=0 then 0 else if mode=1 then
  max (loss 4 1+price mode) (2*price mode-penalty mode) else 2*price mode
def quota (mode : ℕ) := if mode=0 then 27 else 26

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 18000 in
theorem rows : ∀ mode : Fin 3,
    (∀ i : Fin 27,∀ d : Fin 11,∀ j : Fin 3,
      (minimumScore mode i≤RankTable.cap d 3 ∨ d.val=10) →
      (3≤minimumScore mode i → j.val=0 → 4≤d.val) →
      (mode.val=0 → j.val≠2) →
      loss d j+price mode*j.val≤budget mode i+rebate mode j) ∧
    (∀ j : Fin 3,mode.val≠0 → (mode.val=1 → 1≤j.val) → (mode.val=2 → j.val=2) →
      loss 4 j+price mode*j.val≤pivotBill mode+rebate mode j) ∧
    (∑ i∈range (quota mode),budget mode i)+pivotBill mode+penalty mode<
      4*(27:ℕ).choose 9+12*price mode := by
  intro mode; fin_cases mode <;> refine ⟨?_,?_,?_⟩
  all_goals simp only [budget,pivotBill,minimumScore,RankTable.cap,quota,loss,deg,rebate,price,penalty,FiniteRange.badCount]
  all_goals simp only [Nat.choose_eq_fast_choose]
  all_goals decide
end Graffiti384b.EarCredit.Pair
#print axioms Graffiti384b.EarCredit.Pair.rows
