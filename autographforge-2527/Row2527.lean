import Independent
import ThetaDrawing
import Mathlib.Data.Rat.Cast.Order

namespace ThetaIndependent2527
open Finset SimpleGraph TriangleMatching1078 AutoGraphForge378 Theta659

/-- The two hubs form an independent dominating pair. For any proposed
singleton, the hub on the opposite side is distinct and nonadjacent. -/
theorem theta_independent (k : ℕ) : independentDomination (graph k) = 2 := by
  let S : Finset (V k) := {hub false,hub true}
  have neq : (hub false : V k) ≠ hub true := fun eq => Bool.false_ne_true (congrArg Prod.fst eq)
  have size : S.card = 2 := by simp [S,neq]
  have indep : (graph k).IsIndepSet S := by
    intro a ha b hb _ ab
    have casesHub {u : V k} (hu : u ∈ S) : u=hub false ∨ u=hub true := by simpa [S] using hu
    rcases casesHub ha with rfl|rfl <;> rcases casesHub hb with rfl|rfl <;> exact ab
  have dom : Dominates (graph k) S := by
    rintro ⟨b,_|i⟩
    · left; cases b <;> simp [S]
    · right
      refine ⟨hub b,?_,rfl⟩
      cases b <;> simp [S]
  have up : independentDomination (graph k) ≤ 2 := Nat.sInf_le ⟨S,size,indep,dom⟩
  obtain ⟨T,sz,_,domT⟩ := attained (graph k)
  have notZero : T.card ≠ 0 := by
    intro h
    have empty := card_eq_zero.mp h
    rcases domT (hub false) with mem|⟨_,mem,_⟩ <;> simp [empty] at mem
  have notOne : independentDomination (graph k) ≠ 1 := by
    intro one
    obtain ⟨⟨b,i⟩,univAdj⟩ := universal_of_one _ one
    have ne : (hub (!b) : V k) ≠ (b,i) := by
      intro eq
      have same := congrArg Prod.fst eq
      cases b <;> contradiction
    have h := univAdj (hub (!b)) ne
    cases i with
    | none => exact h
    | some j => change (!b)=b at h; cases b <;> contradiction
  omega

/-- Fixing independent domination at two realizes every positive minimum
maximal matching size, on connected planar bipartite graphs. -/
theorem family (k : ℕ) (pos : 0<k) :
    Fintype.card (V k) = 2*k+2 ∧ (graph k).Connected ∧ Theta659.Planar (graph k) ∧
    (graph k).Colorable 2 ∧ independentDomination (graph k) = 2 ∧
    lineDomination (graph k) = k ∧ minMaximalMatching (graph k) = k := by
  obtain ⟨edge,matching⟩ := @matching_exact k
  exact ⟨order k,connected pos,planar k,bipartite,theta_independent k,edge,matching⟩

/-- The catalogue affine expression has exact rational value seven for this
family. Taking k=m+8 makes the excess m+1. -/
theorem unbounded (m : ℕ) :
    2 ≤ Fintype.card (V (m+8)) ∧ (graph (m+8)).Colorable 2 ∧
    (lineDomination (graph (m+8)) : ℚ) =
      (3/4 : ℚ) * independentDomination (graph (m+8)) + 11/2 + (m+1 : ℕ) := by
  obtain ⟨sz,_,_,bip,ind,edge,_⟩ := family (m+8) (by omega)
  refine ⟨by omega,bip,?_⟩
  rw [ind,edge]
  push_cast
  ring

theorem no_bound (f : ℕ → ℕ) : ∃ k : ℕ, (graph k).Connected ∧ Theta659.Planar (graph k) ∧
    (graph k).Colorable 2 ∧ f (independentDomination (graph k)) < lineDomination (graph k) := by
  obtain ⟨_,conn,plane,bip,ind,edge,_⟩ := family (f 2+1) (by omega)
  exact ⟨_,conn,plane,bip,by rw [ind,edge]; omega⟩

theorem row2527_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj],
    2 ≤ Fintype.card U → G.Colorable 2 →
    (lineDomination G : ℚ) ≤ (3/4 : ℚ) * independentDomination G + 11/2) := by
  intro claim
  obtain ⟨sz,bip,eq⟩ := unbounded 0
  have le := claim _ _ sz bip
  norm_num at eq
  linarith

#print axioms family
#print axioms unbounded
#print axioms no_bound
#print axioms row2527_false
end ThetaIndependent2527
