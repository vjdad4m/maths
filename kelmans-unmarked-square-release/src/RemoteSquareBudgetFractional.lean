import RemoteSquareBudgetConditional
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum

namespace KelmansCactus.AtomicBridge.RemoteSquareBudgetFractional
open SimpleGraph Finset
open scoped BigOperators
open RemoteBudgetComponent (Mate cost)
open RemoteRankUnion (Marking)
open RemoteSquareBudgetConditional (Square Decomposition affordable_unmarked_square)
variable {V I ι : Type*} {G : SimpleGraph V}

noncomputable def edgeBit (q : Mate G) (x y : V) : ℕ := by
  classical
  exact if q.mate x=y then 1 else 0

/-- A finite convex decomposition with uniform 1/3 edge marginal.
This is the only use of Edmonds's theorem in the written graph argument;
it remains explicit input rather than a custom axiom. -/
structure UniformMatchingDistribution (G : SimpleGraph V) (ι : Type*) [Fintype ι] where
  target : ι→Mate G
  weight : ι→ℚ
  nonnegative : ∀ i,0≤weight i
  normal : (∑ i : ι,weight i)=1
  marginal : ∀ x y,G.Adj x y →
    (∑ i : ι,weight i*(edgeBit (target i) x y : ℚ))=(1:ℚ)/3

theorem mean_cost [Fintype I] [Fintype ι] (M : Marking G I)
    (D : UniformMatchingDistribution G ι) :
    (∑ i : ι,D.weight i * (cost M (D.target i) : ℚ))=(Fintype.card I : ℚ)/3 := by
  classical
  have each (q : Mate G) : (cost M q : ℚ)=∑ j : I, (edgeBit q (M.a j) (M.b j) : ℚ) := by
    unfold cost edgeBit
    exact Nat.cast_sum _ _
  simp_rw [each,Finset.mul_sum]
  rw [Finset.sum_comm]
  trans ∑ j : I,(1:ℚ)/3
  · apply Finset.sum_congr rfl
    intro j _
    exact D.marginal _ _ (M.edge j)
  · simp [div_eq_mul_inv]

theorem lost_as_bits (p q : Mate G) (A : Square p) :
    (A.lost q : ℚ)=∑ j : Fin 4,(1-(edgeBit q (A.corner j) (p.mate (A.corner j)) : ℚ)) := by
  classical
  unfold Square.lost
  rw [Finset.card_eq_sum_ones,Nat.cast_sum]
  simp only [Nat.cast_one,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : q.mate (A.corner j)=p.mate (A.corner j)
  · simp [Square.openPort,edgeBit,h]
  · simp [Square.openPort,edgeBit,h]

theorem mean_lost [Fintype ι] (p : Mate G) (A : Square p)
    (D : UniformMatchingDistribution G ι) :
    (∑ i : ι,D.weight i*(A.lost (D.target i) : ℚ))=(8:ℚ)/3 := by
  classical
  simp_rw [lost_as_bits,Finset.mul_sum]
  rw [Finset.sum_comm]
  trans ∑ j : Fin 4,(2:ℚ)/3
  · apply Finset.sum_congr rfl
    intro j _
    simp_rw [mul_sub,mul_one,Finset.sum_sub_distrib]
    rw [D.normal,D.marginal _ _ (p.edge _)]
    norm_num
  · norm_num

theorem mean_gain [Fintype I] [Fintype ι] (M : Marking G I) (six : Fintype.card I=6)
    (p : Mate G) (min : ∀ q,cost M p≤cost M q) (atMostOne : cost M p≤1)
    (D : UniformMatchingDistribution G ι) :
    (∑ i : ι,D.weight i*((cost M (D.target i)-cost M p : ℕ) : ℚ))=((2-cost M p : ℕ) : ℚ) := by
  classical
  simp_rw [Nat.cast_sub (min _),mul_sub,Finset.sum_sub_distrib]
  rw [mean_cost M D,six,←Finset.sum_mul,D.normal,one_mul,Nat.cast_sub (by omega)]
  norm_num

theorem from_fractional [Fintype I] [Fintype ι] (M : Marking G I) (six : Fintype.card I=6)
    (p : Mate G) (A : Square p) (min : ∀ q,cost M p≤cost M q) (atMostOne : cost M p≤1)
    (unmarked : ∀ i t,M.a i≠A.corner t) (no : A.NoDiagonal)
    (D : UniformMatchingDistribution G ι) (split : ∀ t,Decomposition A (D.target t)) :
    ∃ q : Mate G,A.lost q=2 ∧ cost M q≤1 :=
  affordable_unmarked_square M p A min atMostOne unmarked no D.target split D.weight D.nonnegative
    (mean_gain M six p min atMostOne D) (mean_lost p A D)

#print axioms from_fractional
end KelmansCactus.AtomicBridge.RemoteSquareBudgetFractional
