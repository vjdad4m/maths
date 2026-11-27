import SixGeometry28

namespace Graffiti384b.FiveBoard28
open Finset SimpleGraph HighSquare28
open Graffiti384b.Port28 (mark)

def rotation (i : ℕ) (f : ℕ→ℕ) := i*f (i-1)+(3-i)*f i

def interior (d i j : ℕ) :=
  3*rotation i (fun t => rotation j (fun h => bill 20 7 d (t+h))) +
  2*(rotation i (bill 20 8 d) + rotation j (bill 20 8 d))

def outsideBill (k d g : ℕ) := if 2≤g then 0 else (20-d).choose k

def boundary (d i j : ℕ) :=
  3*rotation j (fun h => outsideBill 7 d (i+h))+
  2*(outsideBill 8 d i+rotation j (fun h => outsideBill 8 d (1+h)))

def row (i : ℕ) : ℕ :=
  [1951872,1100385,1100385,740025,740025,740025,463320,463320,463320,463320,283140,283140,283140,
   268488,193050,193050,193050,193050,193050,150150,133848,120978,120978,120978,120978,120978][i]?.getD 0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 20000000 in
theorem table :
    (∀ r : Fin 26,∀ d : Fin 20,∀ i j : Fin 4,mark r≤(d.val+(i.val+j.val)).choose 2 →
      (i.val+j.val≤2 → d.val+(i.val+j.val)≤10 → mark r≤RankTable.cap (d.val+(i.val+j.val)) 3) →
      interior d i j≤row r) ∧
    (∀ r : Fin 26,∀ d : Fin 21,∀ i : Fin 3,∀ j : Fin 4,1≤ i.val →
      mark r≤ i.val+(d.val+(i.val+j.val)).choose 2 →
      boundary d i j+95238≤row r) ∧
    (∑ r∈range 26,row r)=11198043 ∧ 11198043 < 6*95238+10814040 := by
  unfold mark row interior boundary rotation outsideBill bill FiniteRange.badCount RankTable.cap
  simp only [Nat.choose_eq_fast_choose]
  decide

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
/-- Count the three ways to omit one candidate according to whether
that candidate was a neighbor of the vertex being charged. -/
theorem rotation_sum {T : Finset V} (size : T.card=3) (w : V) (f : ℕ→ℕ) :
    (∑ x∈T,f (nbr G w (T.erase x)))=rotation (nbr G w T) f := by
  classical
  let A := T.filter (G.Adj w)
  have sub : A⊆T := filter_subset ..
  have er (x : V) : (T.erase x).filter (G.Adj w)=A.erase x := by ext y; simp [A,and_assoc,and_left_comm]
  let h := fun x => f (nbr G w (T.erase x))
  have delta := sum_sdiff sub (f:=h)
  have removed : (∑ x∈A,h x)=A.card*f (A.card-1) := by
    calc _ = ∑ _x∈A,f (A.card-1) := by
             apply sum_congr rfl; intro x xm
             change f ((T.erase x).filter (G.Adj w)).card=_
             rw [er,card_erase_of_mem xm]
         _ = _ := by simp
  have kept : (∑ x∈T\A,h x)=(T\A).card*f A.card := by
    calc _ = ∑ _x∈T\A,f A.card := by
             apply sum_congr rfl; intro x xm
             change f ((T.erase x).filter (G.Adj w)).card=_
             rw [er,erase_eq_of_not_mem (mem_sdiff.mp xm).2]
         _ = _ := by simp
  change (∑ x∈T,h x)=A.card*f (A.card-1)+(3-A.card)*f A.card
  rw [←delta,removed,kept,card_sdiff sub,size,add_comm]

end Graffiti384b.FiveBoard28
#print axioms Graffiti384b.FiveBoard28.table
#print axioms Graffiti384b.FiveBoard28.rotation_sum
