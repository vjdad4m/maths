import TriShort

namespace Graffiti199Depleted.WiderOmission
open CompactOmission
set_option maxRecDepth 8192
set_option maxHeartbeats 13000000

def clausesTriShort1 : List (TreeClause 9) :=
  [⟨448,0,![2,3,4,8,6,5]⟩,
   ⟨960,256,![2,3,4,6,5,7]⟩,
   ⟨102,0,![0,1,2,6,3,7]⟩,
   ⟨45,32,![0,1,2,7,3,4]⟩,
   ⟨45,40,![0,1,2,4,7,8]⟩,
   ⟨451,257,![0,4,3,6,2,5]⟩,
   ⟨70,4,![0,7,6,8,3,2]⟩,
   ⟨66,2,![0,6,5,8,3,2]⟩,
   ⟨960,64,![2,3,6,4,5,7]⟩,
   ⟨153,16,![0,1,2,5,3,4]⟩,
   ⟨411,8,![0,1,4,6,3,5]⟩,
   ⟨153,24,![0,1,2,4,5,8]⟩,
   ⟨327,68,![0,7,6,2,3,4]⟩,
   ⟨451,66,![0,6,2,5,3,4]⟩,
   ⟨960,320,![2,6,4,5,7,8]⟩,
   ⟨303,256,![0,1,6,4,7,3]⟩,
   ⟨564,544,![0,1,2,7,3,5]⟩,
   ⟨327,324,![0,7,6,2,4,8]⟩,
   ⟨451,322,![0,6,2,4,5,8]⟩,
   ⟨451,65,![0,4,3,2,6,5]⟩,
   ⟨451,67,![0,4,6,2,5,8]⟩,
   ⟨451,321,![0,4,6,2,5,8]⟩,
   ⟨582,66,![0,6,2,5,7,3]⟩,
   ⟨153,17,![0,1,4,2,5,8]⟩,
   ⟨564,528,![0,1,2,5,3,7]⟩,
   ⟨5,5,![0,4,7,3,2,8]⟩,
   ⟨576,0,![2,3,8,6,5,7]⟩,
   ⟨960,192,![2,6,5,7,8,4]⟩,
   ⟨153,128,![0,1,2,3,4,5]⟩,
   ⟨153,144,![0,1,2,5,8,4]⟩,
   ⟨153,136,![0,1,2,4,8,5]⟩,
   ⟨582,68,![0,7,6,2,5,3]⟩,
   ⟨564,20,![0,1,7,2,5,3]⟩,
   ⟨640,640,![2,3,4,8,5,7]⟩,
   ⟨129,129,![0,4,3,5,2,8]⟩]

def coverTriShort1 : Cover 9 :=
  (.split 7
  (.split 6
    (.split 8
      ( .other 0)
      (.split 1
        (.split 9
          ( .other 1)
          (.split 2
            (.split 0
              (.split 5
                ( .other 2)
                (.split 3
                  ( .other 3)
                  ( .other 4)))
              ( .other 5))
            ( .other 6)))
        ( .other 7)))
    (.split 0
      (.split 8
        (.split 1
          (.split 2
            (.split 9
              ( .other 8)
              (.split 3
                (.split 5
                  (.split 4
                    ( .other 611)
                    ( .other 9))
                  ( .other 3))
                (.split 4
                  ( .other 10)
                  ( .other 11))))
            ( .other 12))
          ( .other 13))
        (.split 1
          (.split 2
            (.split 9
              ( .other 14)
              (.split 3
                (.split 5
                  ( .other 15)
                  ( .other 3))
                (.split 4
                  (.split 5
                    ( .other 875)
                    ( .other 16))
                  ( .other 11))))
            ( .other 17))
          ( .other 18)))
      (.split 2
        (.split 8
          (.split 1
            ( .other 19)
            ( .other 20))
          (.split 1
            ( .other 21)
            (.split 9
              ( .other 22)
              (.split 4
                (.split 5
                  (.split 3
                    ( .other 870)
                    ( .other 878))
                  ( .other 16))
                (.split 3
                  ( .other 23)
                  (.split 5
                    ( .other 24)
                    ( .other 926)))))))
        ( .other 25))))
  (.split 0
    (.split 9
      (.split 6
        ( .other 26)
        (.split 8
          ( .other 27)
          (.split 2
            (.split 1
              (.split 3
                (.split 4
                  ( .other 28)
                  ( .other 29))
                (.split 5
                  (.split 4
                    ( .other 30)
                    ( .other 507))
                  ( .other 4)))
              ( .other 22))
            (.split 1
              ( .other 31)
              (.split 3
                (.split 4
                  ( .other 28)
                  ( .other 29))
                (.split 4
                  ( .other 30)
                  (.split 5
                    ( .other 32)
                    ( .other 545))))))))
      ( .other 33))
    ( .other 34)))

theorem soundTriShort1 :
    ∀ t : Fin clausesTriShort1.length, (clausesTriShort1.get t).Valid (familyTriShort 1).pattern :=
  fastClauses_sound (by decide +kernel)

theorem validTriShort1 :
    coverTriShort1.Valid (familyTriShort 1).pattern
      (MaskOrClause (familyTriShort 1) clausesTriShort1 (residuesTriShort 1)) 0 0 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · refine ⟨by decide +kernel, ?_, ?_⟩
      · decide +kernel
      · refine ⟨by decide +kernel, ?_, ?_⟩
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
      · refine ⟨by decide +kernel, ?_, ?_⟩
        · decide +kernel
        · decide +kernel
      · decide +kernel
    · decide +kernel

theorem routesTriShort1 (i : Fin (residuesTriShort 1).length) :
    let tag := (residuesTriShort 1).get i
    SegmentRoute seamsTriShort (edgeTriShort 1 tag) (routeTriShort 1 tag) ∨ exceptionalTriShort 1 tag := by
  fin_cases i <;> decide +kernel

end Graffiti199Depleted.WiderOmission
