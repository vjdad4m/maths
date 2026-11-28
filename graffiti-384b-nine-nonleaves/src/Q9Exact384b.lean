import Q9Bridge384b
import Q9Shape0
import Q9Shape1
import Q9Shape2
import Q9Shape3
import Q9Shape4
import Q9Shape5
import Q9TwinShape384b
import Q9Shape7
import Q9Shape8
import Q9Shape9
import Q9Shape10
import Q9Shape11
import Q9Shape12
import Q9Shape13
import Q9Shape14
import Q9Shape15

namespace Graffiti384b.Q9
open SimpleGraph Finset

theorem all_shapes (s : Fin 16) (bits : Nat→Bool)
    (neq : score (adj (forms s) bits) 0 ≠ score (adj (forms s) bits) 1)
    (rank : Ranked (adj (forms s) bits)) :
    ∃ a b c d,Effective (adj (forms s) bits) (adj (forms s) bits) a b c d := by
  fin_cases s
  · exact q9Shape0_cover bits rank
  · exact q9Shape1_cover bits rank
  · exact q9Shape2_cover bits rank
  · exact q9Shape3_cover bits rank
  · exact q9Shape4_cover bits rank
  · exact q9Shape5_cover bits rank
  · exact (neq (true_twins_shape6 bits)).elim
  · exact q9Shape7_cover bits rank
  · exact q9Shape8_cover bits rank
  · exact q9Shape9_cover bits rank
  · exact q9Shape10_cover bits rank
  · exact q9Shape11_cover bits rank
  · exact q9Shape12_cover bits rank
  · exact q9Shape13_cover bits rank
  · exact q9Shape14_cover bits rank
  · exact q9Shape15_cover bits rank

theorem fin9_effective_of_eight_positive_types (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj]
    (diverse : 8 ≤ (trianglePalette G).card) :
    ∃ D : Finset (Fin 9), D.card ≤ 4 ∧ EffectiveSet G D :=
  quota_from_distinct_certificates G all_shapes diverse

/-- Graffiti #384b at exactly nine nonleaves and at least nine triangle-count
types. Isolated vertices, leaves and disconnected graphs are allowed. -/
theorem exact_of_nine_nonleaves {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (nine : (nonleaves G).card = 9) (diverse : 9 ≤ (types G).card) : gamma G ≤ bound G :=
  nonleaf_nine_from_distinct_certificates all_shapes G nine diverse

#print axioms all_shapes
#print axioms fin9_effective_of_eight_positive_types
#print axioms exact_of_nine_nonleaves
end Graffiti384b.Q9
