import Q10Bridge384b
import Q10Shape0
import Q10Shape1
import Q10Shape2
import Q10Shape3
import Q10Shape4
import Q10Shape5
import Q10Shape6
import Q10Shape7
import Q10Shape8
import Q10Shape9
import Q10Shape10
import Q10TwinShape384b
import Q10Shape12
import Q10Shape13
import Q10Shape14
import Q10Shape15
import Q10Shape16
import Q10Shape17
import Q10Shape18
import Q10Shape19
import Q10Shape20
import Q10Shape21
import Q10Shape22
import Q10Shape23
import Q10Shape24
import Q10Shape25
import Q10Shape26
import Q10Shape27
import Q10Shape28

namespace Graffiti384b.Q10
open SimpleGraph Finset

theorem all_shapes (s : Fin 29) (bits : Nat→Bool)
    (neq : score (adj (forms s) bits) 0 ≠ score (adj (forms s) bits) 1)
    (rank : Ranked (adj (forms s) bits)) :
    ∃ a b c d e,Effective (adj (forms s) bits) (adj (forms s) bits) a b c d e := by
  fin_cases s
  · exact q10Shape0_cover bits rank
  · exact q10Shape1_cover bits rank
  · exact q10Shape2_cover bits rank
  · exact q10Shape3_cover bits rank
  · exact q10Shape4_cover bits rank
  · exact q10Shape5_cover bits rank
  · exact q10Shape6_cover bits rank
  · exact q10Shape7_cover bits rank
  · exact q10Shape8_cover bits rank
  · exact q10Shape9_cover bits rank
  · exact q10Shape10_cover bits rank
  · exact (neq (true_twins_shape11 bits)).elim
  · exact q10Shape12_cover bits rank
  · exact q10Shape13_cover bits rank
  · exact q10Shape14_cover bits rank
  · exact q10Shape15_cover bits rank
  · exact q10Shape16_cover bits rank
  · exact q10Shape17_cover bits rank
  · exact q10Shape18_cover bits rank
  · exact q10Shape19_cover bits rank
  · exact q10Shape20_cover bits rank
  · exact q10Shape21_cover bits rank
  · exact q10Shape22_cover bits rank
  · exact q10Shape23_cover bits rank
  · exact q10Shape24_cover bits rank
  · exact q10Shape25_cover bits rank
  · exact q10Shape26_cover bits rank
  · exact q10Shape27_cover bits rank
  · exact q10Shape28_cover bits rank

theorem fin10_effective_of_eight_positive_types (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj]
    (diverse : 8 ≤ (trianglePalette G).card) :
    ∃ D : Finset (Fin 10), D.card ≤ 5 ∧ EffectiveSet G D :=
  quota_from_distinct_certificates G all_shapes diverse

/-- Graffiti #384b at exactly ten nonleaves and nine or ten triangle-count
types. Isolated vertices, leaves and disconnected graphs are allowed. -/
theorem exact_of_ten_nonleaves {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ten : (nonleaves G).card = 10) (diverse : 9 ≤ (types G).card)
    (cap : (types G).card ≤ 10) : gamma G ≤ bound G :=
  nonleaf_ten_from_distinct_certificates all_shapes G ten diverse cap

#print axioms all_shapes
#print axioms fin10_effective_of_eight_positive_types
#print axioms exact_of_ten_nonleaves
end Graffiti384b.Q10
