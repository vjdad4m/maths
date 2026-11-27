import TriShort

namespace Graffiti199Depleted.WiderOmission
open CompactOmission
set_option maxRecDepth 8192
set_option maxHeartbeats 13000000

def clausesTriShort2 : List (TreeClause 9) :=
  [⟨16,0,![0,1,2,8,6,5]⟩,
   ⟨128,0,![2,3,4,8,6,7]⟩,
   ⟨175,128,![0,1,3,4,7,6]⟩,
   ⟨347,16,![0,1,3,5,4,6]⟩,
   ⟨564,48,![0,1,2,5,7,8]⟩,
   ⟨282,272,![0,1,2,5,4,6]⟩,
   ⟨10,8,![0,1,2,4,8,6]⟩,
   ⟨135,132,![0,7,3,6,2,4]⟩,
   ⟨3,1,![0,3,2,4,8,6]⟩,
   ⟨3,2,![0,4,3,2,8,6]⟩,
   ⟨10,2,![0,1,4,2,8,6]⟩,
   ⟨40,8,![1,2,4,8,6,7]⟩,
   ⟨65,1,![0,3,2,8,6,5]⟩,
   ⟨824,56,![1,2,4,5,7,8]⟩]

def coverTriShort2 : Cover 9 :=
  (.split 4
  ( .other 0)
  (.split 7
    ( .other 1)
    (.split 1
      (.split 0
        (.split 2
          (.split 3
            (.split 5
              ( .other 2)
              (.split 8
                (.split 6
                  ( .other 3)
                  (.split 9
                    ( .other 4)
                    ( .other 766)))
                ( .other 5)))
            ( .other 6))
          ( .other 7))
        ( .other 8))
      (.split 0
        ( .other 9)
        (.split 3
          ( .other 10)
          (.split 5
            ( .other 11)
            (.split 6
              ( .other 12)
              (.split 9
                (.split 2
                  ( .other 4)
                  (.split 8
                    ( .other 13)
                    ( .other 525)))
                (.split 2
                  (.split 8
                    ( .other 777)
                    ( .other 1033))
                  (.split 8
                    ( .other 781)
                    ( .other 1037)))))))))))

theorem soundTriShort2 :
    ∀ t : Fin clausesTriShort2.length, (clausesTriShort2.get t).Valid (familyTriShort 2).pattern :=
  fastClauses_sound (by decide +kernel)

theorem validTriShort2 :
    coverTriShort2.Valid (familyTriShort 2).pattern
      (MaskOrClause (familyTriShort 2) clausesTriShort2 (residuesTriShort 2)) 0 0 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · decide +kernel
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · refine ⟨by decide +kernel, ?_, ?_⟩
      · refine ⟨by decide +kernel, ?_, ?_⟩
        · decide +kernel
        · decide +kernel
      · refine ⟨by decide +kernel, ?_, ?_⟩
        · decide +kernel
        · decide +kernel

theorem routesTriShort2 (i : Fin (residuesTriShort 2).length) :
    let tag := (residuesTriShort 2).get i
    SegmentRoute seamsTriShort (edgeTriShort 2 tag) (routeTriShort 2 tag) ∨ exceptionalTriShort 2 tag := by
  fin_cases i <;> decide +kernel

end Graffiti199Depleted.WiderOmission
