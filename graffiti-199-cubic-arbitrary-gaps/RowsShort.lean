import FullMaskCover
import FastTreeCheck
import SparsePlacement
import SegmentSplice

namespace Graffiti199Depleted.WiderOmission

open CompactOmission

def layoutShort : Layout 9 where
  port := ⟨![1,3,7], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  interior := by decide

def familyShort (m : Fin 3) : Family 9 :=
  ![⟨![2,517,10,532,40,16,128,832,128,138],[(0,3),(0,4),(0,5),(0,7),(0,8),(2,5),(2,7),(3,5),(3,6),(3,8),(4,6),(4,7),(5,6),(5,7),(5,8),(6,8)]⟩,
    ⟨![2,517,10,532,40,16,128,832,128,138],[(0,4),(0,5),(0,7),(0,8),(1,4),(1,5),(1,6),(1,8),(2,5),(2,7),(4,6),(4,7),(5,6),(5,7),(5,8),(6,8)]⟩,
    ⟨![2,517,10,532,40,16,128,832,128,138],[(0,3),(0,4),(0,5),(0,8),(1,4),(1,5),(1,6),(1,8),(2,5),(3,5),(3,6),(3,8),(4,6),(5,6),(5,8),(6,8)]⟩] m

def residuesShort (m : Fin 3) : List ℕ := ![[16345,43243,43214,43246,43215,43247,43983,44011,44015],[16124,16380,43559,43815,43575,43831,43767,44023],[24319,16127,32511,36599,52983,44791,61175,40695,57079,48887,65271,36607,52991,44799,61183,40703,57087,48895,65279,36851,36311,36823,36343,36855,49139]] m

private def clausesShort_0 : List (TreeClause 10) :=
  [⟨2560,0,![1,9,3,7,4,8]⟩,
   ⟨2624,512,![1,2,3,4,8,7]⟩,
   ⟨2112,2048,![1,2,9,7,4,8]⟩,
   ⟨2624,64,![1,2,3,7,4,8]⟩,
   ⟨3392,64,![1,2,3,7,4,6]⟩,
   ⟨1283,256,![0,1,2,3,4,6]⟩,
   ⟨1283,257,![0,3,2,4,6,9]⟩,
   ⟨3146,1088,![0,1,2,7,6,4]⟩,
   ⟨3146,1096,![0,7,2,6,9,4]⟩,
   ⟨2138,2112,![0,1,2,7,4,8]⟩,
   ⟨2138,2120,![0,7,2,4,8,9]⟩,
   ⟨35904,2112,![1,2,7,4,6,8]⟩,
   ⟨2138,2128,![0,8,7,2,4,9]⟩,
   ⟨26720,2112,![1,2,7,4,8,5]⟩,
   ⟨61536,8256,![1,2,7,5,6,8]⟩,
   ⟨531,16,![0,1,8,2,3,4]⟩,
   ⟨531,17,![0,3,8,2,4,9]⟩,
   ⟨17056,512,![1,2,3,4,8,5]⟩,
   ⟨34560,1536,![1,2,3,4,8,6]⟩,
   ⟨531,528,![0,8,3,2,4,9]⟩,
   ⟨16438,48,![0,1,8,2,5,4]⟩,
   ⟨16406,20,![0,1,5,8,9,4]⟩,
   ⟨16438,16400,![0,1,8,2,5,4]⟩,
   ⟨38,4,![0,1,5,2,9,4]⟩,
   ⟨16416,16416,![1,2,9,5,4,8]⟩,
   ⟨32784,32784,![0,1,8,2,9,6]⟩,
   ⟨3146,66,![0,1,4,2,7,6]⟩,
   ⟨3146,74,![0,4,7,2,6,9]⟩,
   ⟨3146,2114,![0,4,7,2,6,9]⟩,
   ⟨26624,2048,![1,9,7,4,8,5]⟩,
   ⟨25216,8192,![1,9,3,7,5,8]⟩,
   ⟨38,2,![0,1,4,2,9,5]⟩,
   ⟨12685,8328,![0,1,7,5,6,3]⟩,
   ⟨54144,36992,![1,9,3,5,6,8]⟩,
   ⟨34560,33024,![1,2,3,4,6,8]⟩,
   ⟨34560,33280,![1,2,3,4,8,6]⟩,
   ⟨1283,258,![0,4,3,2,6,9]⟩,
   ⟨17024,512,![1,9,3,4,8,5]⟩,
   ⟨53300,36868,![0,1,5,2,6,8]⟩,
   ⟨54304,36896,![1,2,5,4,6,8]⟩,
   ⟨16438,16386,![0,1,4,2,5,8]⟩,
   ⟨16436,16388,![0,1,5,2,9,8]⟩,
   ⟨1026,1026,![0,1,4,2,9,6]⟩,
   ⟨18,18,![0,1,4,8,2,9]⟩]

private def coveredShort_0 : Cover 10 :=
  .split 6
    (.split 11
      (.split 9
        (.other 0)
        (.other 1))
      (.other 2))
    (.split 1
      (.split 11
        (.split 9
          (.other 3)
          (.split 10
            (.split 8
              (.other 4)
              (.split 0
                (.other 5)
                (.other 6)))
            (.split 3
              (.other 7)
              (.other 8))))
        (.split 4
          (.split 3
            (.other 9)
            (.other 10))
          (.split 15
            (.split 10
              (.other 11)
              (.split 3
                (.other 12)
                (.split 14
                  (.split 2
                    (.split 5
                      (.split 13
                        (.other 13)
                        (.split 12
                          (.other 14)
                          (.split 9
                            (.split 0
                              (.other 15)
                              (.other 16))
                            (.split 7
                              (.other 17)
                              (.split 8
                                (.other 18)
                                (.split 0
                                  (.other 19)
                                  (.other 16389)))))))
                      (.other 20))
                    (.other 21))
                  (.split 5
                    (.split 2
                      (.other 22)
                      (.other 23))
                    (.other 24)))))
            (.other 25))))
      (.split 4
        (.split 10
          (.split 11
            (.split 3
              (.other 26)
              (.other 27))
            (.split 15
              (.other 11)
              (.split 3
                (.other 28)
                (.split 14
                  (.split 13
                    (.other 29)
                    (.split 9
                      (.split 8
                        (.split 7
                          (.other 30)
                          (.split 12
                            (.split 2
                              (.split 5
                                (.other 31)
                                (.split 0
                                  (.other 32)
                                  (.other 43287)))
                              (.split 0
                                (.split 5
                                  (.other 43258)
                                  (.other 43290))
                                (.split 5
                                  (.other 43259)
                                  (.other 43291))))
                            (.other 33)))
                        (.other 34))
                      (.split 8
                        (.other 35)
                        (.split 0
                          (.other 36)
                          (.split 7
                            (.other 37)
                            (.split 5
                              (.split 2
                                (.other 31)
                                (.split 12
                                  (.other 44027)
                                  (.other 38)))
                              (.split 12
                                (.split 2
                                  (.other 44055)
                                  (.other 44059))
                                (.other 39))))))))
                  (.split 5
                    (.split 2
                      (.other 40)
                      (.other 41))
                    (.other 24))))))
          (.other 42))
        (.other 43)))

private def clausesShort_1 : List (TreeClause 10) :=
  [⟨68,0,![0,1,9,3,7,6]⟩,
   ⟨580,64,![0,1,2,6,3,7]⟩,
   ⟨652,512,![0,1,2,3,7,8]⟩,
   ⟨32968,192,![0,1,2,6,8,3]⟩,
   ⟨1105,64,![0,1,2,6,3,4]⟩,
   ⟨1105,80,![0,1,2,4,6,9]⟩,
   ⟨3589,513,![0,4,3,2,7,6]⟩,
   ⟨3589,2561,![0,4,7,2,6,9]⟩,
   ⟨33792,33792,![2,3,4,9,6,8]⟩,
   ⟨2573,520,![0,8,7,2,3,4]⟩,
   ⟨2573,2568,![0,8,7,2,4,9]⟩,
   ⟨9,9,![0,4,8,3,2,9]⟩,
   ⟨516,4,![0,7,6,9,3,2]⟩,
   ⟨3589,516,![0,7,2,6,3,4]⟩,
   ⟨3589,2564,![0,7,2,4,6,9]⟩,
   ⟨33292,516,![0,7,2,6,8,3]⟩,
   ⟨3589,1540,![0,7,2,6,9,4]⟩,
   ⟨1105,1024,![0,1,2,3,4,6]⟩,
   ⟨1105,1088,![0,1,2,6,9,4]⟩,
   ⟨153,24,![0,1,8,2,4,9]⟩,
   ⟨1105,1040,![0,1,2,4,9,6]⟩,
   ⟨5376,1024,![2,3,4,9,5,6]⟩,
   ⟨4450,320,![0,1,2,6,3,5]⟩,
   ⟨4194,96,![0,1,5,6,9,3]⟩,
   ⟨4194,4160,![0,1,6,9,5,3]⟩,
   ⟨12294,4100,![0,7,6,9,5,3]⟩,
   ⟨16395,16392,![0,8,5,4,3,9]⟩,
   ⟨16395,10,![0,5,8,4,3,9]⟩,
   ⟨5123,1026,![0,5,4,3,6,9]⟩,
   ⟨259,2,![0,5,4,3,2,9]⟩,
   ⟨4354,4354,![0,5,2,6,3,9]⟩,
   ⟨3589,517,![0,4,7,2,6,9]⟩,
   ⟨259,1,![0,4,3,5,2,9]⟩,
   ⟨13062,772,![0,7,2,6,3,5]⟩,
   ⟨12294,6,![0,5,7,6,9,3]⟩,
   ⟨12294,8196,![0,7,5,6,9,3]⟩,
   ⟨12384,8192,![1,9,3,7,5,6]⟩,
   ⟨32968,32896,![0,1,2,8,3,6]⟩,
   ⟨32968,32832,![0,1,2,6,3,8]⟩,
   ⟨4194,66,![0,1,5,6,9,3]⟩,
   ⟨1105,65,![0,1,4,2,6,9]⟩,
   ⟨54272,49152,![3,4,9,5,8,6]⟩,
   ⟨54272,36864,![3,4,9,5,6,8]⟩,
   ⟨5123,4097,![0,4,3,5,9,6]⟩,
   ⟨5376,4096,![2,3,4,9,5,6]⟩,
   ⟨33801,33793,![0,4,3,6,2,8]⟩]

private def coveredShort_1 : Cover 10 :=
  .split 2
    (.split 6
      (.other 0)
      (.split 9
        (.other 1)
        (.split 3
          (.split 7
            (.other 2)
            (.split 15
              (.other 3)
              (.split 10
                (.split 0
                  (.split 4
                    (.other 4)
                    (.other 5))
                  (.split 11
                    (.other 6)
                    (.other 7)))
                (.other 8))))
          (.split 0
            (.split 11
              (.other 9)
              (.other 10))
            (.other 11)))))
    (.split 9
      (.other 12)
      (.split 0
        (.split 10
          (.split 11
            (.other 13)
            (.other 14))
          (.split 15
            (.split 3
              (.other 15)
              (.split 11
                (.other 16)
                (.split 1
                  (.split 14
                    (.split 4
                      (.split 6
                        (.other 17)
                        (.other 18))
                      (.split 7
                        (.other 19)
                        (.split 6
                          (.other 20)
                          (.split 12
                            (.split 8
                              (.other 21)
                              (.split 5
                                (.other 22)
                                (.other 23)))
                            (.split 5
                              (.other 24)
                              (.split 13
                                (.other 25)
                                (.split 8
                                  (.other 16170)
                                  (.other 16426))))))))
                    (.other 26))
                  (.split 14
                    (.other 27)
                    (.split 12
                      (.other 28)
                      (.split 8
                        (.other 29)
                        (.other 30)))))))
            (.other 8)))
        (.split 3
          (.split 15
            (.other 15)
            (.split 10
              (.split 11
                (.other 31)
                (.split 12
                  (.split 14
                    (.split 13
                      (.split 1
                        (.split 8
                          (.other 32)
                          (.other 33))
                        (.other 34))
                      (.split 1
                        (.other 35)
                        (.split 6
                          (.split 7
                            (.split 5
                              (.other 36)
                              (.split 4
                                (.split 8
                                  (.other 43605)
                                  (.other 43861))
                                (.split 8
                                  (.other 43621)
                                  (.other 43877))))
                            (.other 37))
                          (.split 7
                            (.other 38)
                            (.split 5
                              (.other 39)
                              (.split 4
                                (.other 40)
                                (.split 8
                                  (.other 43813)
                                  (.other 44069))))))))
                    (.other 41))
                  (.split 14
                    (.other 42)
                    (.split 1
                      (.other 43)
                      (.split 8
                        (.other 44)
                        (.other 30))))))
              (.other 45)))
          (.other 11))))

private def clausesShort_2 : List (TreeClause 10) :=
  [⟨64,0,![0,1,2,9,7,6]⟩,
   ⟨2048,0,![2,3,4,9,7,8]⟩,
   ⟨19,0,![0,1,9,3,7,4]⟩,
   ⟨3,1,![0,3,2,4,9,7]⟩,
   ⟨18,16,![0,1,2,4,9,7]⟩,
   ⟨18,2,![0,1,4,2,9,7]⟩,
   ⟨3,2,![0,4,3,2,9,7]⟩,
   ⟨144,16,![1,2,4,9,7,8]⟩,
   ⟨1025,1,![0,3,2,9,7,6]⟩,
   ⟨304,16,![1,2,4,9,5,7]⟩,
   ⟨292,32,![0,1,2,5,9,7]⟩,
   ⟨773,5,![0,3,5,2,9,7]⟩,
   ⟨32968,192,![0,1,2,6,8,9]⟩,
   ⟨37072,208,![1,2,4,6,8,9]⟩,
   ⟨57824,224,![1,2,5,6,8,9]⟩,
   ⟨8548,320,![0,1,2,6,5,7]⟩,
   ⟨9989,1281,![0,3,2,6,5,7]⟩,
   ⟨61710,33034,![0,4,8,5,6,2]⟩,
   ⟨16652,268,![0,5,8,2,7,9]⟩,
   ⟨12544,4352,![2,5,4,6,7,9]⟩,
   ⟨12550,8450,![0,4,5,2,6,7]⟩,
   ⟨16812,384,![0,1,2,8,5,7]⟩,
   ⟨19213,2305,![0,3,2,8,5,7]⟩,
   ⟨16654,266,![0,4,8,5,7,2]⟩,
   ⟨8452,8452,![0,5,2,6,7,9]⟩,
   ⟨16640,16640,![2,5,4,8,7,9]⟩]

private def coveredShort_2 : Cover 10 :=
  .split 6
    (.other 0)
    (.split 11
      (.other 1)
      (.split 1
        (.split 4
          (.split 0
            (.other 2)
            (.other 3))
          (.other 4))
        (.split 4
          (.other 5)
          (.split 0
            (.other 6)
            (.split 7
              (.other 7)
              (.split 10
                (.other 8)
                (.split 8
                  (.split 5
                    (.other 9)
                    (.split 2
                      (.other 10)
                      (.split 9
                        (.other 11)
                        (.split 15
                          (.split 3
                            (.other 12)
                            (.split 12
                              (.other 13)
                              (.split 13
                                (.split 14
                                  (.other 14)
                                  (.other 24345))
                                (.split 14
                                  (.other 16153)
                                  (.other 32537)))))
                          (.split 3
                            (.split 12
                              (.split 13
                                (.split 14
                                  (.other 36625)
                                  (.other 53009))
                                (.split 14
                                  (.other 44817)
                                  (.other 61201)))
                              (.split 13
                                (.split 14
                                  (.other 40721)
                                  (.other 57105))
                                (.split 14
                                  (.other 48913)
                                  (.other 65297))))
                            (.split 12
                              (.split 13
                                (.split 14
                                  (.other 36633)
                                  (.other 53017))
                                (.split 14
                                  (.other 44825)
                                  (.other 61209)))
                              (.split 13
                                (.split 14
                                  (.other 40729)
                                  (.other 57113))
                                (.split 14
                                  (.other 48921)
                                  (.other 65305)))))))))
                  (.split 14
                    (.split 13
                      (.split 12
                        (.split 15
                          (.other 13)
                          (.split 2
                            (.split 3
                              (.split 5
                                (.other 15)
                                (.split 9
                                  (.other 16)
                                  (.other 36877)))
                              (.other 17))
                            (.split 3
                              (.split 5
                                (.split 9
                                  (.other 36337)
                                  (.other 36849))
                                (.split 9
                                  (.other 36369)
                                  (.other 36881)))
                              (.other 18))))
                        (.other 19))
                      (.split 2
                        (.split 3
                          (.split 15
                            (.other 12)
                            (.split 12
                              (.other 20)
                              (.split 5
                                (.other 21)
                                (.split 9
                                  (.other 22)
                                  (.other 49165)))))
                          (.other 23))
                        (.other 24)))
                    (.other 25)))))))))


private def clausesShort (m : Fin 3) : List (TreeClause 10) :=
  ![clausesShort_0,clausesShort_1,clausesShort_2] m

private def coveredShort (m : Fin 3) : Cover 10 :=
  ![coveredShort_0,coveredShort_1,coveredShort_2] m

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

private theorem clausesShort_valid0 :
    ∀ t : Fin (clausesShort 0).length, ((clausesShort 0).get t).Valid (familyShort 0).pattern :=
  fastClauses_sound (by decide +kernel)

private theorem coveredShort_valid0 :
    (coveredShort 0).Valid (familyShort 0).pattern
      (MaskOrClause (familyShort 0) (clausesShort 0) (residuesShort 0)) 0 0 := by decide +kernel

private theorem clausesShort_valid1 :
    ∀ t : Fin (clausesShort 1).length, ((clausesShort 1).get t).Valid (familyShort 1).pattern :=
  fastClauses_sound (by decide +kernel)

private theorem coveredShort_valid1 :
    (coveredShort 1).Valid (familyShort 1).pattern
      (MaskOrClause (familyShort 1) (clausesShort 1) (residuesShort 1)) 0 0 := by decide +kernel

private theorem clausesShort_valid2 :
    ∀ t : Fin (clausesShort 2).length, ((clausesShort 2).get t).Valid (familyShort 2).pattern :=
  fastClauses_sound (by decide +kernel)

private theorem coveredShort_valid2 :
    (coveredShort 2).Valid (familyShort 2).pattern
      (MaskOrClause (familyShort 2) (clausesShort 2) (residuesShort 2)) 0 0 := by decide +kernel

private theorem clausesShort_valid (m : Fin 3) :
    ∀ i : Fin (clausesShort m).length, ((clausesShort m).get i).Valid (familyShort m).pattern := by
  fin_cases m
  · exact clausesShort_valid0
  · exact clausesShort_valid1
  · exact clausesShort_valid2

private theorem coveredShort_valid (m : Fin 3) :
    (coveredShort m).Valid (familyShort m).pattern
      (MaskOrClause (familyShort m) (clausesShort m) (residuesShort m)) 0 0 := by
  fin_cases m
  · exact coveredShort_valid0
  · exact coveredShort_valid1
  · exact coveredShort_valid2

theorem classificationShort (m : Fin 3) (row : ℕ) :
    (∃ T, SixTree ((familyShort m).pattern.edge row) T) ∨
      ∃ tag ∈ residuesShort m, ∀ i j,
        (familyShort m).pattern.edge row i j = (familyShort m).pattern.edge tag i j :=
  classified_with_full_mask (clausesShort_valid m) (coveredShort_valid m) row

theorem familyShort_consistent (m : Fin 3) : SparseConsistent layoutShort [5] m (familyShort m) := by
  fin_cases m <;> decide

def edgeShort (m : Fin 3) (tag : ℕ) : Fin 10 → Fin 10 → Bool := (familyShort m).pattern.edge tag

#print axioms classificationShort
#print axioms familyShort_consistent

def seamsShort : Seams 9 1 := ![(5,6)]

private def pathsShort (m : Fin 3) : List (ℕ × List (SegmentToken 9 1)) :=
  ![[(43243,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 4,.across 0 false,.vertex 8]),
      (43214,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 4,.across 0 false,.vertex 8]),
      (43246,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 4,.across 0 false,.vertex 8]),
      (43215,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 4,.across 0 false,.vertex 8]),
      (43247,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 4,.across 0 false,.vertex 8]),
      (43983,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 4,.across 0 false,.vertex 8]),
      (44011,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 4,.across 0 false,.vertex 8]),
      (44015,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 4,.across 0 false,.vertex 8])],
    [(16380,[.vertex 0,.vertex 1,.vertex 2,.across 0 false,.vertex 4,.vertex 3,.vertex 9,.vertex 7,.vertex 8]),
      (43559,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 4,.across 0 false,.vertex 8]),
      (43815,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 4,.across 0 false,.vertex 8]),
      (43575,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 4,.across 0 false,.vertex 8]),
      (43831,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 4,.across 0 false,.vertex 8]),
      (43767,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 4,.across 0 false,.vertex 8]),
      (44023,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 4,.across 0 false,.vertex 8])],
    [(24319,[.vertex 0,.vertex 4,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.across 0 true,.vertex 8]),
      (16127,[.vertex 0,.vertex 4,.across 0 false,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 8]),
      (32511,[.vertex 0,.vertex 4,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.across 0 true,.vertex 8]),
      (36599,[.vertex 0,.vertex 4,.across 0 false,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 8]),
      (52983,[.vertex 0,.vertex 4,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.across 0 true,.vertex 8]),
      (44791,[.vertex 0,.vertex 4,.across 0 false,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 8]),
      (61175,[.vertex 0,.vertex 4,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.across 0 true,.vertex 8]),
      (40695,[.vertex 0,.vertex 4,.across 0 false,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 8]),
      (57079,[.vertex 0,.vertex 4,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.across 0 true,.vertex 8]),
      (48887,[.vertex 0,.vertex 4,.across 0 false,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 8]),
      (65271,[.vertex 0,.vertex 4,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.across 0 true,.vertex 8]),
      (36607,[.vertex 0,.vertex 4,.across 0 false,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 8]),
      (52991,[.vertex 0,.vertex 4,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.across 0 true,.vertex 8]),
      (44799,[.vertex 0,.vertex 4,.across 0 false,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 8]),
      (61183,[.vertex 0,.vertex 4,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.across 0 true,.vertex 8]),
      (40703,[.vertex 0,.vertex 4,.across 0 false,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 8]),
      (57087,[.vertex 0,.vertex 4,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.across 0 true,.vertex 8]),
      (48895,[.vertex 0,.vertex 4,.across 0 false,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.vertex 8]),
      (65279,[.vertex 0,.vertex 4,.vertex 1,.vertex 2,.vertex 3,.vertex 9,.vertex 7,.across 0 true,.vertex 8]),
      (36851,[.vertex 0,.vertex 4,.vertex 1,.vertex 2,.across 0 false,.vertex 3,.vertex 9,.vertex 7,.vertex 8]),
      (36311,[.vertex 0,.vertex 4,.vertex 1,.vertex 2,.across 0 false,.vertex 3,.vertex 9,.vertex 7,.vertex 8]),
      (36823,[.vertex 0,.vertex 4,.vertex 1,.vertex 2,.across 0 false,.vertex 3,.vertex 9,.vertex 7,.vertex 8]),
      (36343,[.vertex 0,.vertex 4,.vertex 1,.vertex 2,.across 0 false,.vertex 3,.vertex 9,.vertex 7,.vertex 8]),
      (36855,[.vertex 0,.vertex 4,.vertex 1,.vertex 2,.across 0 false,.vertex 3,.vertex 9,.vertex 7,.vertex 8]),
      (49139,[.vertex 0,.vertex 1,.vertex 2,.across 0 false,.vertex 4,.vertex 3,.vertex 9,.vertex 7,.vertex 8])]] m

def routeShort (m : Fin 3) (tag : ℕ) : List (SegmentToken 9 1) :=
  ((pathsShort m).lookup tag).getD []

def ShortResidual (m : Fin 3) (tag : ℕ) : Prop :=
  (m = 0 ∧ tag = 16345) ∨ (m = 1 ∧ tag = 16124)

instance shortResidualDecidable (m : Fin 3) (tag : ℕ) : Decidable (ShortResidual m tag) := by
  unfold ShortResidual
  infer_instance

private def ValidRoutesShort (m : Fin 3) : Prop :=
  ∀ i : Fin (residuesShort m).length,
    let tag := (residuesShort m).get i
    ShortResidual m tag ∨ SegmentRoute seamsShort (edgeShort m tag) (routeShort m tag)

instance validRoutesShortDecidable (m : Fin 3) : Decidable (ValidRoutesShort m) := by
  unfold ValidRoutesShort
  infer_instance

private theorem routesShort_0 : ValidRoutesShort 0 := by decide +kernel
private theorem routesShort_1 : ValidRoutesShort 1 := by decide +kernel
private theorem routesShort_2 : ValidRoutesShort 2 := by decide +kernel

theorem certifiedRouteShort (m : Fin 3) {tag : ℕ} (h : tag ∈ residuesShort m) :
    ShortResidual m tag ∨ SegmentRoute seamsShort (edgeShort m tag) (routeShort m tag) := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp h
  fin_cases m
  · exact routesShort_0 i
  · exact routesShort_1 i
  · exact routesShort_2 i

#print axioms certifiedRouteShort

end Graffiti199Depleted.WiderOmission
