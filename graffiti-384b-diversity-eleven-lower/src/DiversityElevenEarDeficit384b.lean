import DiversityElevenEarFootprint384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Independent low vertices in a failing lower profile have at most one
deficit in their combined high-neighbor footprint. -/
theorem deficit_one_of_independent_low (t : (types G).card=11)
    (nine : (high G).card=9) (bad : bound G<gamma G)
    {X P : Finset V} (low : Disjoint X (high G))
    (deg : ∀ x∈X,2≤G.degree x) (ind : ∀ x∈X,∀ y∈X,¬G.Adj x y)
    (touch : ∀ z∈high G,(∃ x∈X,G.Adj x z)→z∈P) :
    2*X.card≤P.card+1 := by
  by_contra! win
  exact (not_le_of_gt bad) (exact_of_ear_footprint G t nine low deg ind touch (by omega))

/-- A failure at diversity eleven with independent low vertices in the
triangle skeleton has at most five such nonisolated low vertices. -/
theorem at_most_five_independent_low (t : (types G).card=11)
    (nine : (high G).card=9) (bad : bound G<gamma G)
    (ind : ∀ x∈nonleaves G \ high G,∀ y∈nonleaves G \ high G,¬G.Adj x y) :
    (nonleaves G \ high G).card≤5 := by
  have h := deficit_one_of_independent_low G t nine bad
    (X := nonleaves G \ high G) (P := high G)
    (Finset.disjoint_left.mpr (fun _ a b => (mem_sdiff.mp a).2 b))
    (fun x hx => (mem_filter.mp (mem_sdiff.mp hx).1).2) ind
    (fun _ hz _ => hz)
  omega

#print axioms deficit_one_of_independent_low
#print axioms at_most_five_independent_low
end Graffiti384b.DiversityEleven
