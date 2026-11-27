import TriCompact

namespace Graffiti199Depleted.WiderOmission
open CompactOmission
set_option maxRecDepth 8192
set_option maxHeartbeats 13000000

def clausesTriCompact0 : List (TreeClause 8) :=
  [⟨8,0,![1,2,7,5,4,6]⟩,
   ⟨14,8,![0,1,2,5,4,6]⟩,
   ⟨14,10,![0,5,2,4,6,7]⟩,
   ⟨14,12,![0,6,5,2,4,7]⟩,
   ⟨21,4,![0,1,6,2,3,4]⟩,
   ⟨21,20,![0,6,3,2,4,7]⟩,
   ⟨21,5,![0,3,6,2,4,7]⟩]

def coverTriCompact0 : Cover 8 :=
  (.split 3
  ( .other 0)
  (.split 2
    (.split 1
      ( .other 1)
      ( .other 2))
    (.split 1
      ( .other 3)
      (.split 0
        (.split 4
          ( .other 4)
          ( .other 5))
        (.split 4
          ( .other 6)
          ( .other 38))))))

theorem soundTriCompact0 :
    ∀ t : Fin clausesTriCompact0.length, (clausesTriCompact0.get t).Valid (familyTriCompact 0).pattern :=
  fastClauses_sound (by decide +kernel)

theorem validTriCompact0 :
    coverTriCompact0.Valid (familyTriCompact 0).pattern
      (MaskOrClause (familyTriCompact 0) clausesTriCompact0 (residuesTriCompact 0)) 0 0 := by
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

theorem routesTriCompact0 (i : Fin (residuesTriCompact 0).length) :
    let tag := (residuesTriCompact 0).get i
    SegmentRoute seamsTriCompact (edgeTriCompact 0 tag) (routeTriCompact 0 tag) ∨ exceptionalTriCompact 0 tag := by
  (fin_cases i; decide +kernel)

end Graffiti199Depleted.WiderOmission
