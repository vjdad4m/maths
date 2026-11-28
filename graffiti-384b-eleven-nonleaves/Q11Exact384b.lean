import Q11Ambient384b
import Q11Shape0
import Q11Shape1
import Q11Shape2
import Q11Shape3
import Q11Shape4
import Q11Shape5
import Q11Shape6
import Q11Shape7
import Q11Shape8
import Q11Shape9
import Q11Shape10
import Q11Shape11
import Q11Shape12
import Q11Shape13
import Q11Shape14
import Q11Shape15
import Q11Shape16
import Q11Shape17
import Q11Shape18
import Q11Shape19
import Q11Shape20
import Q11Shape21
import Q11Shape22
import Q11Shape23
import Q11Shape24
import Q11Shape25
import Q11Shape26
import Q11Shape27
import Q11Shape28
import Q11Shape29
import Q11Shape30
import Q11Shape31
import Q11Shape32
import Q11Shape33
import Q11Shape34
import Q11Shape35
import Q11Shape36
import Q11Shape37
import Q11Shape38
import Q11Shape39
import Q11Shape40
import Q11Shape41
import Q11Shape42
import Q11Shape43
import Q11Shape44
import Q11Shape45

namespace Graffiti384b.EffectiveSearch.Q11
open SimpleGraph Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem all_shapes (s : Fin 46) (bits : Nat→Bool)
    (rank : Ranked (adj 11 (forms s) bits) (root (n:=11) (by decide))) :
    ∃ D : Finset (Label 11),D.card≤6 ∧
      Effective (adj 11 (forms s) bits) (adj 11 (forms s) bits) D := by
  fin_cases s
  · exact q11Shape0_cover bits rank
  · exact q11Shape1_cover bits rank
  · exact q11Shape2_cover bits rank
  · exact q11Shape3_cover bits rank
  · exact q11Shape4_cover bits rank
  · exact q11Shape5_cover bits rank
  · exact q11Shape6_cover bits rank
  · exact q11Shape7_cover bits rank
  · exact q11Shape8_cover bits rank
  · exact q11Shape9_cover bits rank
  · exact q11Shape10_cover bits rank
  · exact q11Shape11_cover bits rank
  · exact q11Shape12_cover bits rank
  · exact q11Shape13_cover bits rank
  · exact q11Shape14_cover bits rank
  · exact q11Shape15_cover bits rank
  · exact q11Shape16_cover bits rank
  · exact q11Shape17_cover bits rank
  · exact q11Shape18_cover bits rank
  · exact q11Shape19_cover bits rank
  · exact q11Shape20_cover bits rank
  · exact q11Shape21_cover bits rank
  · exact q11Shape22_cover bits rank
  · exact q11Shape23_cover bits rank
  · exact q11Shape24_cover bits rank
  · exact q11Shape25_cover bits rank
  · exact q11Shape26_cover bits rank
  · exact q11Shape27_cover bits rank
  · exact q11Shape28_cover bits rank
  · exact q11Shape29_cover bits rank
  · exact q11Shape30_cover bits rank
  · exact q11Shape31_cover bits rank
  · exact q11Shape32_cover bits rank
  · exact q11Shape33_cover bits rank
  · exact q11Shape34_cover bits rank
  · exact q11Shape35_cover bits rank
  · exact q11Shape36_cover bits rank
  · exact q11Shape37_cover bits rank
  · exact q11Shape38_cover bits rank
  · exact q11Shape39_cover bits rank
  · exact q11Shape40_cover bits rank
  · exact q11Shape41_cover bits rank
  · exact q11Shape42_cover bits rank
  · exact q11Shape43_cover bits rank
  · exact q11Shape44_cover bits rank
  · exact q11Shape45_cover bits rank

theorem exact_of_nine_types {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : (nonleaves G).card = 11) (diverse : (types G).card=9) : gamma G≤bound G :=
  exact_of_nine_types_from_covers all_shapes G order diverse

#print axioms all_shapes
#print axioms exact_of_nine_types
end Graffiti384b.EffectiveSearch.Q11
