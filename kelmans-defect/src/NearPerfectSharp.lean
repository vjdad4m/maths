import NearPerfectCells

open Finset
namespace KelmansCactus.NearPerfectSharp
open ThreePort

def score (w : ℕ) : ℕ := if w=1 then 2 else if w=2 then 0 else 1

private theorem score_le (w : ℕ) : score w≤2 := by
  unfold score
  split
  · omega
  · split <;> omega

private theorem score_opp {a b : ℕ} (h : Opposite a b) : score a+score b=2 := by
  rcases h with ⟨rfl,rfl⟩|⟨a1,a2,b1,b2,sum⟩
  · decide
  · have both : (a=1 ∧ b=2) ∨ (a=2 ∧ b=1) := by omega
    rcases both with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

private theorem fin_three_sum (f : Fin 3→ℕ) :
    (∑ j : Fin 3,f j)= f 0 + f 1 + f 2 := by
  have univ3 : (univ:Finset (Fin 3))={0,1,2} := by decide
  rw [univ3,sum_insert (by decide : (0:Fin 3)∉({1,2}:Finset (Fin 3))),
      sum_insert (by decide : (1:Fin 3)∉({2}:Finset (Fin 3))),sum_singleton]
  omega

/-- A bad residue-two cell has score at most 2+2h. With no
hole the unique width multiset is 2,2,1, giving score 2.
With one hole the width sum is 1 mod 3 and score at most 4.
With at least two holes, the crude score bound 6 suffices. -/
theorem cell_score (w : Fin 3→ℕ) (h : ℕ)
    (bounds : ∀ i,w i≤2) (res : ((∑ i,w i)+h)%3=2)
    (bad : h=0 → (∑ i,w i)≠2) :
    (∑ i,score (w i))≤2+2*h := by
  rw [fin_three_sum] at res bad ⊢
  by_cases hh : 2≤h
  · have a := score_le (w 0)
    have b := score_le (w 1)
    have c := score_le (w 2)
    omega
  · have a := bounds 0
    have b := bounds 1
    have c := bounds 2
    have small : ∀ x : ℕ, x≤2 → x=0 ∨ x=1 ∨ x=2 := by intro x hx; omega
    rcases small _ a with p|p|p <;> rcases small _ b with q|q|q <;>
      rcases small _ c with r|r|r <;> simp only [p,q,r] at res bad ⊢ <;>
      simp [score] <;> omega

/-- Sharp endpoint accounting: thanks to the exact complementary
seam widths, the predicted vacancy cost doubles compared with the
capacity-only bound. There is one actual vacancy per two cells. -/
theorem ports_force_half_defect {I : Type*} [Fintype I] [DecidableEq I]
    (w : I×Fin 3→ℕ) (mate : I×Fin 3→I×Fin 3)
    (pair : Function.Involutive mate)
    (opp : ∀ s, Opposite (w s) (w (mate s)))
    (bounds : ∀ s,w s≤2)
    (h : I→ℕ) (res : ∀ i, ((∑ j : Fin 3,w (i,j))+h i)%3=2)
    (bad : ∀ i,h i=0 → (∑ j : Fin 3,w (i,j))≠2) :
    Fintype.card I ≤ 2*(∑ i,h i) := by
  classical
  have perm :
      (∑ s : I×Fin 3, score (w (mate s))) =
      (∑ s : I×Fin 3, score (w s)) := by
    exact Equiv.sum_comp pair.toPerm (fun s=>score (w s))
  have total : (∑ s : I×Fin 3, score (w s)) = 3*Fintype.card I := by
    have split := sum_add_distrib (s:= (univ:Finset (I×Fin 3)))
      (f:=fun s=>score (w s)) (g:=fun s=>score (w (mate s)))
    rw [perm] at split
    have v : (∑ s : I×Fin 3, (score (w s) + score (w (mate s)))) =
        2*(3*Fintype.card I) := by
      simp_rw [score_opp (opp _)]
      simp [Nat.mul_comm]
    rw [v] at split
    omega
  have localSum :
      (∑ i : I,∑ j : Fin 3,score (w (i,j))) ≤
      (∑ i : I, (2+2*h i)) :=
    sum_le_sum (fun i _=>cell_score (fun j=>w (i,j)) (h i)
      (fun j=>bounds (i,j)) (res i) (bad i))
  rw [←Fintype.sum_prod_type (fun s=>score (w s)),total] at localSum
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,card_univ] at localSum
  change 3*Fintype.card I ≤ Fintype.card I*2 + 2*∑ i,h i at localSum
  omega

#print axioms cell_score
#print axioms ports_force_half_defect
end KelmansCactus.NearPerfectSharp
