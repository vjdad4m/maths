import Reduction182
import Reduction183
import OrderBridge

namespace Graffiti182
open Finset SimpleGraph
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem peripheral_degree_le_square_degree :
    peripheralSquareMaxDegree G ≤ Graffiti183.squareMaxDegree G := by
  classical
  unfold peripheralSquareMaxDegree
  apply Finset.sup_le_iff.mpr
  intro v _
  have sub : peripheralNeighbors G v ⊆ (square G).neighborFinset v := by
    intro w hw
    exact ((square G).mem_neighborFinset v w).mpr (mem_filter.mp hw).2
  have count := card_le_card sub
  rw [card_neighborFinset_eq_degree] at count
  exact count.trans ((square G).degree_le_maxDegree v)

variable [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj]

/-- The only metric case where the elementary order bound is inadequate
has square periphery equal to all vertices, so #183 subsumes it. -/
theorem claim_of_183 (hc : G.Connected) (h183 : Graffiti183.Claim183 G) :
    Claim182 G := by
  classical
  have hbound : Fintype.card V + 1 ≤ maxLeaves G + bipartiteNumber G :=
    Graffiti185.Reuse.order_bound G hc
  apply conjecture182_from_order_bounds hc hbound
  intro hd hp hf
  obtain ⟨v,w,hvw,hfa⟩ := hf
  have sqVW : (square G).dist v w = 2 := by
    rw [square_dist hc,hvw]
  have eV : 2 ≤ eccentricity (square G) v :=
    sqVW ▸ le_sup (f := (square G).dist v) (mem_univ w)
  have dV : 2 ≤ diameter (square G) :=
    eV.trans (le_sup (f := eccentricity (square G)) (mem_univ v))
  have hrad : 2 ≤ Graffiti183.radius (Graffiti183.square G) := by
    unfold Graffiti183.radius
    refine le_csInf ⟨_, Set.mem_range_self v⟩ ?_
    rintro x ⟨u,rfl⟩
    have hu : u ∈ periphery (square G) := hp ▸ (mem_univ u)
    have he := (mem_filter.mp hu).2
    change 2 ≤ eccentricity (square G) u
    rw [he]
    exact dV
  have compare := peripheral_degree_le_square_degree G
  unfold Graffiti183.Claim183 at h183
  change _ ≤ maxLeaves G + bipartiteNumber G at h183
  have mlo : Fintype.card V + 1 < peripheralSquareMaxDegree G + diameter G :=
    (metric_excess_iff hc).mpr ⟨hd,hp,v,w,hvw,hfa⟩
  omega

#print axioms claim_of_183
end Graffiti182
