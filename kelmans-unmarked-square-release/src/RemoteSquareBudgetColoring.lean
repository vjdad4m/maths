import RemoteSquareBudgetFractional

namespace KelmansCactus.AtomicBridge.RemoteSquareBudgetColoring
open SimpleGraph Finset
open scoped BigOperators
open RemoteBudgetComponent (Mate cost)
open RemoteSquareBudgetFractional (edgeBit UniformMatchingDistribution)
variable {V : Type*} {G : SimpleGraph V}

def TriplePartition (q : Fin 3→Mate G) : Prop :=
  ∀ x y,G.Adj x y → ∃ j : Fin 3, (q j).mate x=y ∧
    ∀ k : Fin 3,(q k).mate x=y → k=j

/-- Three edge-disjoint perfect matchings covering every edge give an explicit
uniform fractional distribution; no matching-polytope theorem is required. -/
noncomputable def uniform_of_three (q : Fin 3→Mate G) (cover : TriplePartition q) :
    UniformMatchingDistribution G (Fin 3) := by
  classical
  refine ⟨q,fun _=>(1:ℚ)/3,fun _=>by norm_num,by norm_num,?_⟩
  intro x y e
  obtain ⟨j,same,unique⟩ := cover x y e
  have rules (k : Fin 3) : (q k).mate x=y ↔ k=j :=
    ⟨unique k,fun r=>r.symm ▸ same⟩
  have bit (k : Fin 3) : ((edgeBit (q k) x y : ℕ) : ℚ)= if k=j then 1 else 0 := by
    unfold edgeBit
    simp [rules k]
  simp_rw [bit,←Finset.mul_sum]
  simp

#print axioms uniform_of_three
end KelmansCactus.AtomicBridge.RemoteSquareBudgetColoring
