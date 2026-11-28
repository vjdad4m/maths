import Q8GraphTransfer384b
import Q8Original384b
import Q8Shape0384b
import Q8Shape1384b
import Q8Shape2384b
import Q8Shape3384b
import Q8Shape4384b
import Q8Shape5384b
import Q8Shape6384b
import Q8Shape7384b

namespace Graffiti384b.Q8
open SimpleGraph Finset

/-- A graph on eight vertices with pairwise distinct positive triangle counts
always has a two-dominating set of size at most three. -/
theorem fin8_positive_distinct_quota
    (G : SimpleGraph (Fin 8)) (dh : DecidableRel G.Adj) :
    letI := dh
    (∀ v,0<trianglesAt G v) → Function.Injective (trianglesAt G) → gamma G ≤ 3 := by
  letI := dh
  intro positive distinct
  apply core8_of_covers G ?_ positive distinct
  intro s b H
  fin_cases s
  · exact q8Shape0_cover b H
  · exact q8Shape1_cover b H
  · exact q8Shape2_cover b H
  · exact q8Shape3_cover b H
  · exact q8Shape4_cover b H
  · exact q8Shape5_cover b H
  · exact q8Shape6_cover b H
  · exact q8Shape7_cover b H

/-- The catalogue inequality at eight nonleaves and at least nine
triangle-count types, including zero. Connectivity is not required. -/
theorem exact_of_eight_nonleaves {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (eight : (nonleaves G).card=8) (nine : 9≤(types G).card) :
    gamma G≤bound G :=
  Q8Original.nonleaf_eight_of_fin8_quota fin8_positive_distinct_quota G eight nine

#print axioms fin8_positive_distinct_quota
#print axioms exact_of_eight_nonleaves
end Graffiti384b.Q8
