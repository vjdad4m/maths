import TwoEdgeTable34_384b

namespace Graffiti384b.CrossFour34
open Finset SimpleGraph CliqueChoice CliqueSample LowSample
open private LowSample.delta from LowSample384b

def shift (m : ℕ) := min (LowSample.delta m 10 8) (FiniteRange.badCount m 10 8-(m-8).choose 10-Finish33.rebate m 10)
def rate (m j : ℕ) := LowSample.delta m 10 j - (if j=8 then shift m else 0)
def base (m : ℕ) := FiniteRange.badCount m 10 9+shift m
def refund (m : ℕ) := Finish33.rebate m 10 + shift m
def degreeRank (m d : ℕ) := ∑ j∈range 9,if d≤j then rate m j else 0
def rank (m : ℕ) (h : Bool) (t : ℕ) := ∑ j∈range 9,if t<TwoEdge34.ceiling h j then rate m j else 0
def charge (m : ℕ) (L : ℕ → ℕ) := m*base m+∑ j∈range 9,rate m j*L j

def firstPay : ℕ → Bool → ℕ
  | 22, _ => 119977
  | 23, _ => 294151
  | 24, h => if h then 669240 else 634062
  | 25, h => if h then 1409148 else 1248988
  | 26, h => if h then 2629968 else 2359838
  | 27, h => if h then 4572898 else 4294268
  | 28, h => if h then 7731328 else 7553678
  | 29, _ => 12740089
  | _, _ => 0
def secondPay : ℕ → Bool → ℕ
  | 22, _ => 45760
  | 23, _ => 128128
  | 24, _ => 320320
  | 25, _ => 732160
  | 26, _ => 1555840
  | 27, _ => 3077646
  | 28, _ => 5794620
  | 29, _ => 10455510
  | _, _ => 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
theorem rates : ∀ k : Fin 8, ∀ h : Bool, ∀ d : Fin 34,3≤d.val →
    let m := 29-k.val
    (2≤d.val/2 → firstPay m h≤rank m h (d.val/2)+d.val*refund m) ∧
    (2≤1+(d.val-2).choose 2 → secondPay m h≤rank m h (1+(d.val-2).choose 2)+d.val*refund m) ∧
    FiniteRange.badCount m 10 (min d.val 9) ≤ base m+degreeRank m d.val ∧
    (m-min d.val 9).choose 10+refund m ≤ base m+degreeRank m d.val := by
  unfold firstPay secondPay rank TwoEdge34.ceiling base degreeRank rate refund shift Finish33.rebate LowSample.delta FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
theorem budget : ∀ f∈Boundary.levels.powerset,
    let m := 29-f.card
    let h := decide (3∈f)
    f.card≤7 ∧ 9<m ∧ 16*m.choose 10+charge m (SharedRanks34.limit f)+(5+f.card)*refund m <
    (m-10+1)*m.choose 10+(m-2).choose 8+(∑ d∈f,bonus m 10 d)+firstPay m h+secondPay m h := by
  unfold firstPay secondPay charge SharedRanks34.limit slots rate base refund shift Finish33.rebate LowSample.delta bonus FiniteRange.badCount
  simp only [FiniteRange.badCount,Nat.choose_eq_fast_choose]
  decide
end Graffiti384b.CrossFour34
#print axioms Graffiti384b.CrossFour34.rates
#print axioms Graffiti384b.CrossFour34.budget

