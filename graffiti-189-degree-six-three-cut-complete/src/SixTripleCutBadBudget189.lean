import SixTripleCutForeignCharge189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Abstract charge once the exceptional terminal spends a unit on
its sole low port's internal neighbor. -/
theorem exceptional_port_charge {S : Finset V} {t : V}
    (ss : S.card = 3) (ts : t ∈ S) {pA pB pC qA qB qC : V → ℕ}
    (a : ∑ u∈S,pA u ≤ 6) (b : ∑ u∈S,pB u ≤ 6)
    (a1 : pA t = 1) (aq : 1 ≤ qA t)
    (ag : ∀ u∈S, u ≠ t → 5 ≤ pA u+qA u)
    (bg : ∀ u∈S, 5 ≤ pB u+qB u)
    (q : ∀ u∈S, qA u+qB u+qC u ≤ 6)
    (p : pB t+pC t ≤ 6) :
    (∑ u∈S,qC u) ≤ 3 ∧ pC t+qC t ≤ 6 := by
  have e : (S.erase t).card = 2 := by rw [card_erase_of_mem ts,ss]
  have aa := sum_le_sum (s:=S.erase t) (f:=fun _=>(5:ℕ))
    (g:=fun u=>pA u+qA u) (fun u hu=>ag u (mem_erase.mp hu).2 (mem_erase.mp hu).1)
  have ae : (∑ _u∈S.erase t,(5:ℕ)) = 10 := by simp [e]
  rw [ae,sum_add_distrib] at aa
  have ea := sum_erase_add S pA ts
  have eq := sum_erase_add S qA ts
  have bb := sum_le_sum (s:=S) (f:=fun _=>(5:ℕ))
    (g:=fun u=>pB u+qB u) (fun u hu=>bg u hu)
  have be : (∑ _u∈S,(5:ℕ)) = 15 := by simp [ss]
  rw [be,sum_add_distrib] at bb
  have qq := sum_le_sum (s:=S) (f:=fun u=>qA u+qB u+qC u)
    (g:=fun _=>(6:ℕ)) (fun u hu=>q u hu)
  have qe : (∑ _u∈S,(6:ℕ)) = 18 := by simp [ss]
  rw [qe,sum_add_distrib,sum_add_distrib] at qq
  constructor
  · omega
  · have ht := q t ts
    have hb := bg t ts
    omega

#print axioms exceptional_port_charge
end Graffiti189LongestPath.ThresholdSix.ThreeCut
