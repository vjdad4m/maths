import DiversityElevenProfile384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A small high-anchor footprint lets independent ears supply the extra
odd-palette omission. In particular a three-edge connected piece of
the auxiliary high-anchor ear graph cannot occur. -/
theorem exact_of_ear_footprint (t : (types G).card=11) (nine : (high G).card=9)
    {X P : Finset V} (low : Disjoint X (high G))
    (deg : ∀ x∈X,2≤G.degree x) (ind : ∀ x∈X,∀ y∈X,¬G.Adj x y)
    (touch : ∀ z∈high G,(∃ x∈X,G.Adj x z)→z∈P)
    (small : P.card+2≤2*X.card) : gamma G≤bound G := by
  apply Repair.exact_of_low_support G X low deg ind
  have cap := card_le_card (show (high G).filter (fun z=>∃ x∈X,G.Adj x z) ⊆ P from
    fun z zm=>(touch z (mem_filter.mp zm).1 (mem_filter.mp zm).2))
  omega

theorem exact_of_three_ears_four_anchors (t : (types G).card=11) (nine : (high G).card=9)
    {X P : Finset V} (low : Disjoint X (high G))
    (deg : ∀ x∈X,2≤G.degree x) (ind : ∀ x∈X,∀ y∈X,¬G.Adj x y)
    (touch : ∀ z∈high G,(∃ x∈X,G.Adj x z)→z∈P)
    (three : 3≤X.card) (four : P.card≤4) : gamma G≤bound G :=
  exact_of_ear_footprint G t nine low deg ind touch (by omega)

#print axioms exact_of_ear_footprint
end Graffiti384b.DiversityEleven
