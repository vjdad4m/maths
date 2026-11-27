import FourPool28
namespace Graffiti384b.Four28
open Finset
def fullPrice (k : ℕ) := if k=1 then 3 else 1
def seedPrice (k : ℕ) := if k=1 then 7 else 4
def extra (k : ℕ) := if k=1 then 6864396 else 2558160

/-- Rank charges for one retained vertex or the two retained neighbors of the
unique score-one vertex. In the latter case rank zero needs no seeded repair. -/
def charge (k h i : ℕ) : ℕ :=
  let row : List ℕ := if k=1 then
    (if h=8 then [41513252,33668228,26803832,25673978,18958808,18580898,12883178,12883178,12815348,8431592,8431592,8431592,5284994,5284994,5284994,5284994,3145714,3145714,3145714,3145714,3145714,3145714,3145714,3145714,3145714,3145714,3145714,1768624]
     else [41513252,33668228,26803832,25673978,18958808,18580898,12883178,12883178,12815348,8431592,8431592,8431592,5284994,5284994,5284994,5284994,3145714,3145714,3145714,3145714,3140852,1784354,1784354,1784354,1784354,1784354,1784354,1768624])
    else (if h=8 then [7354710,11710688,9152528,8844386,6402506,6324986,4309466,4309466,4299776,2788136,2788136,2788136,1729988,1729988,1729988,1729988,1025882,1025882,1025882,1025882,1025882,990418,990418,990418,990418,990418,990418,539968]
          else [7354710,11710688,9152528,8844386,6402506,6324986,4309466,4309466,4299776,2788136,2788136,2788136,1729988,1729988,1729988,1729988,1025882,1025882,1025882,1025882,1025882,578578,578578,578578,578578,578578,578578,539968])
  row[i]?.getD 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 15000000 in
theorem charge_rows : ∀ k∈({1,2}:Finset ℕ),∀ h∈({8,9}:Finset ℕ),∀ i : Fin 28,∀ d : Fin 11,
    (i.val+1≤RankTable.cap d 3 ∨ d.val=10) →
    let u := fullPrice k*FiniteRange.badCount 28 10 d
    let n := 28-k
    let a := seedPrice k*FiniteRange.badCount n 9 d
    u≤charge k h i ∧ ((k≠2 ∨ i.val≠0) →
      (u+seedPrice k*(n-d.val).choose 9≤charge k h i) ∧
      ((i.val+1≤RankTable.cap d 2 ∨ h<d.val) → u+a≤charge k h i) ∧
      u+a≤charge k h i+extra k) := by
  unfold charge extra fullPrice seedPrice RankTable.cap FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide

theorem totals : ∀ k∈({1,2}:Finset ℕ),∀ h∈({8,9}:Finset ℕ),
    (∑ i∈range 28,charge k h i)+(h-8)*extra k <
    fullPrice k*((28:ℕ).choose 10*4)+seedPrice k*((28-k).choose 9*(5-k)) := by
  unfold charge extra fullPrice seedPrice
  simp only [Nat.choose_eq_fast_choose]
  decide
end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.charge_rows
#print axioms Graffiti384b.Four28.totals
