import ShoreSample28
namespace Graffiti384b.Core28
open Finset

def leftDraw (a : ℕ) := if a=6 then 2 else if a=8 then 3 else if a=10 then 3 else if a=12 then 4 else 5
def rightDraw (a : ℕ) := if a=6 then 8 else if a=8 then 7 else if a=10 then 6 else if a=12 then 6 else 5
def leftPrice (a : ℕ) := if a=6 then 21318 else if a=8 then 7752 else if a=10 then 26299 else if a=12 then 2912 else 1
def rightPrice (a : ℕ) := if a=6 then 5 else if a=8 then 7 else if a=10 then 200 else if a=12 then 225 else 1
def leftShift (a : ℕ) := if a=6 then 546924 else if a=8 then 84084 else if a=10 then 106400 else if a=12 then 10052 else 0

def leftCost (a i : ℕ) := leftPrice a*fee a (leftDraw a) (1+i)+leftShift a
def rightCost (a i : ℕ) := rightPrice a*fee (28-a) (rightDraw a) (1+i)
def rankCost (a i : ℕ) := if floorD (1+i)<a then max (leftCost a i) (rightCost a i) else rightCost a i

set_option maxRecDepth 32768 in
private theorem dual_table : ∀ a : Fin 15,6≤a.val → a.val%2=0 →
    (∑ i∈range 28,rankCost a i) <
       leftPrice a*(a.val.choose (leftDraw a)*(a.val/2-leftDraw a)) + a.val*leftShift a +
       rightPrice a*((28-a.val).choose (rightDraw a)*((28-a.val)/2-rightDraw a)) := by
  unfold rankCost leftCost rightCost leftPrice rightPrice leftShift fee leftDraw rightDraw floorD FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide

/-- Joint bounds for complementary sets of ranks at every even split from
six plus twenty-two through fourteen plus fourteen. -/
theorem no_two_budgets {A B : Finset ℕ} (a : ℕ) (lo : 6≤a) (hi : a≤14) (ev : a%2=0)
    (an : A.card=a) (dis : Disjoint A B) (cover : A∪B=range 28)
    (fits : ∀ i∈A,floorD (1+i)<a)
    (left : a.choose (leftDraw a)*(a/2-leftDraw a)≤∑ i∈A,fee a (leftDraw a) (1+i))
    (right : (28-a).choose (rightDraw a)*((28-a)/2-rightDraw a)≤∑ i∈B,fee (28-a) (rightDraw a) (1+i)) : False := by
  have L := Nat.mul_le_mul_left (leftPrice a) left
  have R := Nat.mul_le_mul_left (rightPrice a) right
  have bl : ∑ i∈A,leftCost a i=leftPrice a*(∑ i∈A,fee a (leftDraw a) (1+i))+a*leftShift a := by
    simp [leftCost,sum_add_distrib,mul_sum,an]
  have br : ∑ i∈B,rightCost a i=rightPrice a*(∑ i∈B,fee (28-a) (rightDraw a) (1+i)) := by
    simp [rightCost,mul_sum]
  have leftCap : (∑ i∈A,leftCost a i)≤∑ i∈A,rankCost a i :=
    sum_le_sum (fun i im => by simp only [rankCost,if_pos (fits i im)]; exact le_max_left ..)
  have rightCap : (∑ i∈B,rightCost a i)≤∑ i∈B,rankCost a i :=
    sum_le_sum (fun i _ => by unfold rankCost; split_ifs <;> simp)
  have joint := Nat.add_le_add leftCap rightCap
  rw [←sum_union dis,cover,bl,br] at joint
  have row := dual_table ⟨a,by omega⟩ lo ev
  change (∑ i∈range 28,rankCost a i) <
       leftPrice a*(a.choose (leftDraw a)*(a/2-leftDraw a)) + a*leftShift a +
       rightPrice a*((28-a).choose (rightDraw a)*((28-a)/2-rightDraw a)) at row
  omega

end Graffiti384b.Core28
#print axioms Graffiti384b.Core28.no_two_budgets
