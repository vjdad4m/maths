import TriCompact

namespace Graffiti199Depleted.WiderOmission
open CompactOmission
set_option maxRecDepth 8192
set_option maxHeartbeats 13000000

def clausesTriCompact1 : List (TreeClause 8) :=
  [⟨15,0,![0,1,5,4,6,3]⟩,
   ⟨19,1,![0,5,4,6,3,2]⟩,
   ⟨19,17,![0,5,2,4,6,7]⟩,
   ⟨14,8,![0,1,2,6,3,4]⟩,
   ⟨27,0,![0,1,2,5,3,6]⟩,
   ⟨14,12,![0,1,2,4,6,7]⟩,
   ⟨14,2,![0,1,6,2,3,4]⟩,
   ⟨19,2,![0,6,5,4,3,2]⟩,
   ⟨19,18,![0,6,5,2,4,7]⟩,
   ⟨14,6,![0,1,6,2,4,7]⟩]

def coverTriCompact1 : Cover 8 :=
  (.split 1
  (.split 2
    (.split 3
      (.split 0
        ( .other 0)
        (.split 4
          ( .other 1)
          ( .other 2)))
      ( .other 3))
    (.split 3
      (.split 0
        (.split 4
          ( .other 4)
          ( .other 30))
        (.split 4
          ( .other 1)
          ( .other 2)))
      ( .other 5)))
  (.split 2
    (.split 3
      ( .other 6)
      (.split 4
        (.split 0
          ( .other 7)
          ( .other 21))
        (.split 0
          ( .other 8)
          ( .other 37))))
    (.split 3
      ( .other 9)
      (.split 4
        (.split 0
          ( .other 7)
          ( .other 25))
        (.split 0
          ( .other 8)
          ( .other 41))))))

theorem soundTriCompact1 :
    ∀ t : Fin clausesTriCompact1.length, (clausesTriCompact1.get t).Valid (familyTriCompact 1).pattern :=
  fastClauses_sound (by decide +kernel)

theorem validTriCompact1 :
    coverTriCompact1.Valid (familyTriCompact 1).pattern
      (MaskOrClause (familyTriCompact 1) clausesTriCompact1 (residuesTriCompact 1)) 0 0 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · refine ⟨by decide +kernel, ?_, ?_⟩
      · refine ⟨by decide +kernel, ?_, ?_⟩
        · decide +kernel
        · decide +kernel
      · decide +kernel
    · refine ⟨by decide +kernel, ?_, ?_⟩
      · refine ⟨by decide +kernel, ?_, ?_⟩
        · decide +kernel
        · decide +kernel
      · decide +kernel
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · refine ⟨by decide +kernel, ?_, ?_⟩
      · decide +kernel
      · refine ⟨by decide +kernel, ?_, ?_⟩
        · decide +kernel
        · decide +kernel
    · refine ⟨by decide +kernel, ?_, ?_⟩
      · decide +kernel
      · refine ⟨by decide +kernel, ?_, ?_⟩
        · decide +kernel
        · decide +kernel

theorem routesTriCompact1 (i : Fin (residuesTriCompact 1).length) :
    let tag := (residuesTriCompact 1).get i
    SegmentRoute seamsTriCompact (edgeTriCompact 1 tag) (routeTriCompact 1 tag) ∨ exceptionalTriCompact 1 tag := by
  fin_cases i <;> decide +kernel

end Graffiti199Depleted.WiderOmission
