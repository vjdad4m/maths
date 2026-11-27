import PairSeparationAtOrders
import OneAndThree

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

/-- In the covered order-15/16 layout, separating just the singleton
high sets is enough to apply the traceability theorem. -/
theorem traceable_at_fifteen_or_sixteen_of_singleton_separation
    (F : FourBlockPacking G)
    (pHigh : ∀ u ∈ pairPorts F.depleted, G.degree u ≠ 3)
    (sDis : Disjoint (singletonPorts F.first) (singletonPorts F.second))
    (noSix : NoIndependentSix G) (connected : G.Connected)
    (conn : vertexConnectivity G = 3) (budget : treeNumber G ≤ 5)
    (order : Fintype.card V = 15 ∨ Fintype.card V = 16) :
    Traceable G := by
  classical
  have pDis := F.pair_highs_disjoint_at_fifteen_or_sixteen pHigh sDis budget connected order
  exact traceable_at_fifteen_or_sixteen_of_separated_four_blocks
    F ⟨sDis,pDis,pHigh⟩ noSix conn budget order

#print axioms traceable_at_fifteen_or_sixteen_of_singleton_separation

end Graffiti199Depleted.Catalogue
