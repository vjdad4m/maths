import TriCompact

namespace Graffiti199Depleted.WiderOmission
open CompactOmission
set_option maxRecDepth 8192
set_option maxHeartbeats 13000000

def clausesTriCompact2 : List (TreeClause 8) :=
  [⟨4,0,![0,1,2,7,5,4]⟩,
   ⟨14,4,![0,1,2,4,5,6]⟩,
   ⟨14,12,![0,1,2,4,6,7]⟩,
   ⟨14,6,![0,1,6,2,4,7]⟩,
   ⟨19,2,![0,6,5,4,3,2]⟩,
   ⟨19,18,![0,6,3,2,4,7]⟩,
   ⟨19,3,![0,3,6,2,4,7]⟩]

def coverTriCompact2 : Cover 8 :=
  (.split 2
  ( .other 0)
  (.split 1
    (.split 3
      ( .other 1)
      ( .other 2))
    (.split 3
      ( .other 3)
      (.split 0
        (.split 4
          ( .other 4)
          ( .other 5))
        (.split 4
          ( .other 6)
          ( .other 38))))))

theorem soundTriCompact2 :
    ∀ t : Fin clausesTriCompact2.length, (clausesTriCompact2.get t).Valid (familyTriCompact 2).pattern :=
  fastClauses_sound (by decide +kernel)

theorem validTriCompact2 :
    coverTriCompact2.Valid (familyTriCompact 2).pattern
      (MaskOrClause (familyTriCompact 2) clausesTriCompact2 (residuesTriCompact 2)) 0 0 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · decide +kernel
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · refine ⟨by decide +kernel, ?_, ?_⟩
      · decide +kernel
      · decide +kernel
    · refine ⟨by decide +kernel, ?_, ?_⟩
      · decide +kernel
      · refine ⟨by decide +kernel, ?_, ?_⟩
        · decide +kernel
        · decide +kernel

theorem routesTriCompact2 (i : Fin (residuesTriCompact 2).length) :
    let tag := (residuesTriCompact 2).get i
    SegmentRoute seamsTriCompact (edgeTriCompact 2 tag) (routeTriCompact 2 tag) ∨ exceptionalTriCompact 2 tag := by
  (fin_cases i; decide +kernel)

end Graffiti199Depleted.WiderOmission
