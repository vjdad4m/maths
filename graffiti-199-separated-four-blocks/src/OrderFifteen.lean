import OwnershipSplice
import FourLossFromCatalogue

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
variable (F : FourBlockPacking G)

/-- Relabel the two paired blocks while keeping their singleton owners. -/
def FourBlockPacking.swapPairs (H : FourBlockSeparation F) : FourBlockPacking G where
  first := F.first
  second := F.second
  depleted := F.terminal
  terminal := F.depleted
  looseFirst := F.looseFirst
  looseSecond := F.looseSecond
  lowDistinct := by
    let perm : Fin 6 → Fin 6 := ![0,1,4,5,2,3]
    have pinj : Function.Injective perm := by
      unfold Function.Injective
      decide
    let low : Fin 6 → V := ![F.first.f 0,F.second.f 0,F.depleted.f 0,F.depleted.f 1,
      F.terminal.f 0,F.terminal.f 1]
    have eq : (![F.first.f 0,F.second.f 0,F.terminal.f 0,F.terminal.f 1,
      F.depleted.f 0,F.depleted.f 1] : Fin 6 → V) = low ∘ perm := by
      funext i
      fin_cases i <;> rfl
    rw [eq]
    exact F.lowDistinct.comp pinj
  highDegree := fun v hv => hv.elim (fun h => F.highDegree v (Or.inl h)) (H.depletedDegree v)
  cover := fun v => (F.cover v).imp id (Or.imp id Or.symm)

theorem FourBlockPacking.swapPairs_separation (H : FourBlockSeparation F) :
    FourBlockSeparation (F.swapPairs H) :=
  ⟨H.singletons,H.pairs.symm,fun v h => F.highDegree v (Or.inr h)⟩

namespace Catalogue

/-- The recovered order-fifteen two-pair branch with disjoint highs is
traceable at the exact connectivity-three and induced-tree budget. -/
theorem traceable_at_fifteen_of_separated_four_blocks
    (H : FourBlockSeparation F) (noSix : NoIndependentSix G)
    (conn : vertexConnectivity G = 3) (budget : treeNumber G ≤ 5)
    (order : Fintype.card V = 15) : Traceable G := by
  classical
  by_contra hn
  rcases F.four_losses_at_fifteen H noSix order hn with ⟨a,_⟩|⟨_,b⟩
  · exact hn (traceable_of_depleted_pair_of_tree_budget F conn budget
      (F.highs_owned_of_four_losses _ a) (by omega))
  · exact hn (traceable_of_depleted_pair_of_tree_budget (F.swapPairs H) conn budget
      (F.highs_owned_of_four_losses _ b) (by omega))

#print axioms traceable_at_fifteen_of_separated_four_blocks

end Catalogue
end Graffiti199Depleted
