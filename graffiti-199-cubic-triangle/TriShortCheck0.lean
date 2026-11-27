import TriShort

namespace Graffiti199Depleted.WiderOmission
open CompactOmission
set_option maxRecDepth 8192
set_option maxHeartbeats 13000000

def clausesTriShort0 : List (TreeClause 9) :=
  [⟨20,0,![0,1,2,8,6,5]⟩,
   ⟨336,0,![1,2,3,4,6,7]⟩,
   ⟨75,64,![0,1,2,3,4,7]⟩,
   ⟨75,65,![0,3,2,4,7,8]⟩,
   ⟨406,6,![0,1,4,6,2,5]⟩,
   ⟨400,128,![1,2,8,6,5,4]⟩,
   ⟨272,256,![1,2,8,6,4,7]⟩,
   ⟨540,16,![0,1,2,6,5,7]⟩,
   ⟨163,32,![0,1,2,3,4,5]⟩,
   ⟨335,1,![0,1,3,4,6,7]⟩,
   ⟨406,144,![0,1,2,6,5,4]⟩,
   ⟨286,272,![0,1,2,6,4,7]⟩,
   ⟨286,18,![0,1,4,2,6,7]⟩,
   ⟨286,274,![0,4,6,2,7,8]⟩,
   ⟨540,20,![0,6,2,5,7,8]⟩,
   ⟨335,4,![0,1,6,3,7,4]⟩,
   ⟨747,577,![0,1,3,4,7,5]⟩,
   ⟨163,33,![0,3,2,4,5,8]⟩,
   ⟨406,148,![0,6,2,5,8,4]⟩,
   ⟨286,276,![0,6,2,4,7,8]⟩,
   ⟨406,22,![0,4,6,2,5,8]⟩,
   ⟨736,576,![1,2,3,4,7,5]⟩,
   ⟨163,34,![0,4,3,2,5,8]⟩,
   ⟨736,544,![1,2,3,4,5,7]⟩,
   ⟨650,642,![0,1,4,2,5,7]⟩,
   ⟨528,0,![1,2,8,6,5,7]⟩,
   ⟨540,24,![0,7,6,2,5,8]⟩,
   ⟨75,8,![0,1,7,2,3,4]⟩,
   ⟨75,72,![0,7,3,2,4,8]⟩,
   ⟨75,9,![0,3,7,2,4,8]⟩,
   ⟨736,96,![1,2,3,4,5,7]⟩,
   ⟨912,272,![1,2,6,4,5,7]⟩,
   ⟨912,144,![1,2,6,5,7,4]⟩,
   ⟨163,129,![0,3,2,4,8,5]⟩,
   ⟨10,10,![0,1,4,7,2,8]⟩,
   ⟨520,520,![0,1,7,2,8,5]⟩]

def coverTriShort0 : Cover 9 :=
  (.split 3
  (.split 4
    (.split 8
      (.split 2
        ( .other 0)
        (.split 7
          (.split 1
            (.split 6
              ( .other 1)
              (.split 0
                ( .other 2)
                ( .other 3)))
            ( .other 4))
          ( .other 5)))
      ( .other 6))
    (.split 2
      (.split 9
        ( .other 7)
        (.split 1
          (.split 8
            (.split 7
              (.split 6
                (.split 0
                  (.split 5
                    ( .other 564)
                    ( .other 8))
                  ( .other 9))
                (.split 0
                  ( .other 2)
                  ( .other 3)))
              ( .other 10))
            ( .other 11))
          (.split 8
            ( .other 12)
            ( .other 13))))
      (.split 9
        ( .other 14)
        (.split 1
          (.split 8
            (.split 7
              (.split 0
                (.split 6
                  ( .other 15)
                  ( .other 2))
                (.split 5
                  (.split 6
                    ( .other 569)
                    ( .other 16))
                  ( .other 17)))
              ( .other 18))
            ( .other 19))
          (.split 7
            (.split 8
              ( .other 20)
              (.split 5
                (.split 6
                  (.split 0
                    ( .other 826)
                    ( .other 827))
                  ( .other 21))
                (.split 0
                  ( .other 22)
                  (.split 6
                    ( .other 23)
                    ( .other 923)))))
            ( .other 24))))))
  (.split 9
    (.split 4
      ( .other 25)
      (.split 1
        (.split 2
          ( .other 26)
          (.split 7
            (.split 8
              (.split 0
                (.split 6
                  ( .other 27)
                  ( .other 28))
                (.split 6
                  ( .other 29)
                  (.split 5
                    ( .other 129)
                    ( .other 30))))
              ( .other 31))
            (.split 8
              ( .other 32)
              (.split 0
                (.split 6
                  ( .other 27)
                  ( .other 28))
                (.split 5
                  ( .other 33)
                  (.split 6
                    ( .other 29)
                    ( .other 545)))))))
        ( .other 34)))
    ( .other 35)))

theorem soundTriShort0 :
    ∀ t : Fin clausesTriShort0.length, (clausesTriShort0.get t).Valid (familyTriShort 0).pattern :=
  fastClauses_sound (by decide +kernel)

theorem validTriShort0 :
    coverTriShort0.Valid (familyTriShort 0).pattern
      (MaskOrClause (familyTriShort 0) clausesTriShort0 (residuesTriShort 0)) 0 0 := by
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
      · refine ⟨by decide +kernel, ?_, ?_⟩
        · decide +kernel
        · decide +kernel
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · refine ⟨by decide +kernel, ?_, ?_⟩
      · decide +kernel
      · refine ⟨by decide +kernel, ?_, ?_⟩
        · decide +kernel
        · decide +kernel
    · decide +kernel

theorem routesTriShort0 (i : Fin (residuesTriShort 0).length) :
    let tag := (residuesTriShort 0).get i
    SegmentRoute seamsTriShort (edgeTriShort 0 tag) (routeTriShort 0 tag) ∨ exceptionalTriShort 0 tag := by
  fin_cases i <;> decide +kernel

end Graffiti199Depleted.WiderOmission
