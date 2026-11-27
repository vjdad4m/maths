import NoLeafAttachment
import LeafFinish

namespace Graffiti384b.OrderThirtyThree
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The full order-33 profile at diversity 31 with exactly 32 nonleaves. -/
theorem exact (n : Fintype.card V=33) (q : (nonleaves G).card=32)
    (t : (types G).card=31) : gamma G≤bound G := by
  classical
  by_contra! bad
  obtain ⟨u,v,du,dv,uv⟩ := Shared.leaf_necessary G n q t bad
  have ind (a b : V) (da : G.degree a=2) (db : G.degree b=2) : ¬G.Adj a b :=
    fun ab => (not_lt_of_ge (AdjacentFull.exact G n q t ab da db)) bad
  exact (not_lt_of_ge (LeafPath.exact_leaf G n q t ind du dv uv)) bad

#print axioms Graffiti384b.OrderThirtyThree.exact
end Graffiti384b.OrderThirtyThree
