import Frontier31Finish

namespace Graffiti384b.Frontier31.DegreeRows
open Finset SimpleGraph CliqueChoice CliqueSample LowSample
open private Repair.triangles_le_choose from Repair384b
open private LowSample.delta LowSample.weight from LowSample384b
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b

def tracked (skip j : ℕ) : Prop := 5≤j ∧ j≤8 ∧ j≠skip
instance (skip j : ℕ) : Decidable (tracked skip j) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def capAt (skip j : ℕ) := if tracked skip j then RankTable.cap j 3 else j.choose 2
def countAt (skip h : ℕ) (f : Finset ℕ) (j : ℕ) :=
  min (h-f.card) (h+min (slots f j Boundary.levels) (capAt skip j+1)-31-(f.filter (·≤j)).card)
def required (skip : ℕ) := if skip=0 then 31 else 32
theorem cap_mono : ∀ k : Fin 9,∀ a b : Fin 11,a.val≤b.val → capAt k a≤capAt k b := by decide

def row (skip h : ℕ) (f : Finset ℕ) :=
  let m := h-f.card
  12≤m ∧ envelope m 11 ∧ reward m 11 ∧
  6*(15*m.choose 11+UnifiedSample.chargeAt m 11 (countAt skip h f)) <
    6*(m-11)*m.choose 11+(required skip-h)*(6*(m-2).choose 9)+6*(∑ d∈f,bonus m 11 d)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 64000000 in
theorem rows : ∀ skip∈({0,5,6,7,8}:Finset ℕ),∀ h∈({29,30}:Finset ℕ),
    ∀ f∈Boundary.levels.powerset,row skip h f := by
  unfold row required countAt capAt tracked envelope reward UnifiedSample.chargeAt LowSample.delta LowSample.weight
    bonus slots Boundary.levels FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide

end Graffiti384b.Frontier31.DegreeRows
#print axioms Graffiti384b.Frontier31.DegreeRows.rows
