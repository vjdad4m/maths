import FullMaskCover

namespace Graffiti199Depleted.WiderOmission

open CompactOmission

def layout34 : Layout 10 where
  port := ⟨![1,4,8], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  interior := by decide

def family34 (m : Fin 3) : Family 10 :=
  ![⟨![2,1029,10,20,1064,80,160,320,1664,256,274],[(0,2),(0,4),(0,5),(0,6),(0,8),(0,9),(2,4),(2,6),(2,7),(2,8),(3,5),(3,6),(3,8),(3,9),(4,6),(4,7),(4,9),(5,7),(5,8),(6,8),(6,9),(7,9)]⟩,
    ⟨![2,1029,10,20,1064,80,160,320,1664,256,274],[(0,2),(0,5),(0,6),(0,8),(0,9),(1,3),(1,5),(1,6),(1,7),(1,9),(2,6),(2,7),(2,8),(3,5),(3,6),(3,8),(3,9),(5,7),(5,8),(6,8),(6,9),(7,9)]⟩,
    ⟨![2,1029,10,20,1064,80,160,320,1664,256,274],[(0,2),(0,4),(0,5),(0,6),(0,9),(1,3),(1,5),(1,6),(1,7),(1,9),(2,4),(2,6),(2,7),(3,5),(3,6),(3,9),(4,6),(4,7),(4,9),(5,7),(6,9),(7,9)]⟩] m

def residues34 (m : Fin 3) : List ℕ := ![[1045075,1045106,1045107,1047251],[958456,974840,835576,966648,851960,983032],[2557934,3082222,3606510,4130798,2557950,3606526,985086,3082238,2033662,4130814,2564078,3100646]] m

private def clauses34_0 : List (TreeClause 11) :=
  [⟨267264,0,![1,10,4,8,3,5]⟩,
   ⟨425984,0,![1,10,4,8,5,7]⟩,
   ⟨164864,32768,![1,10,4,3,5,7]⟩,
   ⟨398336,135168,![1,10,8,3,7,5]⟩,
   ⟨262656,262144,![1,2,10,8,5,9]⟩,
   ⟨275968,262656,![1,2,3,8,5,9]⟩,
   ⟨275456,266240,![1,10,8,3,5,9]⟩,
   ⟨275456,270336,![1,10,8,5,9,3]⟩,
   ⟨398336,266240,![1,10,8,3,5,7]⟩,
   ⟨164864,131072,![1,10,4,3,5,7]⟩,
   ⟨74752,8192,![1,10,4,3,5,9]⟩,
   ⟨65600,65536,![1,2,10,4,5,9]⟩,
   ⟨4112,4096,![0,1,10,8,3,7]⟩,
   ⟨32770,32768,![0,1,10,4,3,7]⟩,
   ⟨1130688,65600,![1,2,4,5,9,6]⟩,
   ⟨1835648,262656,![1,2,8,5,9,6]⟩,
   ⟨8225,8192,![0,1,2,10,3,9]⟩,
   ⟨1060013,8197,![0,2,5,3,6,9]⟩,
   ⟨3156393,8201,![0,2,6,3,7,9]⟩,
   ⟨1059884,8228,![0,1,5,9,6,3]⟩,
   ⟨3156008,8232,![0,1,6,9,7,3]⟩,
   ⟨1059968,1056768,![1,2,3,9,6,5]⟩,
   ⟨3200,2048,![1,2,10,3,6,5]⟩,
   ⟨1059968,8320,![1,2,3,6,9,5]⟩,
   ⟨141,128,![0,1,2,10,6,5]⟩,
   ⟨1835068,262160,![0,1,8,5,9,6]⟩,
   ⟨1130542,65538,![0,1,4,5,9,6]⟩,
   ⟨1059884,10244,![0,1,5,6,3,9]⟩,
   ⟨3156008,10272,![0,1,9,3,6,7]⟩,
   ⟨2056,2056,![0,1,6,10,3,7]⟩,
   ⟨1048704,1048704,![1,2,10,6,5,9]⟩,
   ⟨2237696,2236416,![1,2,3,9,7,5]⟩,
   ⟨132352,131328,![1,2,10,3,7,5]⟩,
   ⟨267776,1024,![1,2,10,3,8,5]⟩,
   ⟨275968,1536,![1,2,3,8,5,9]⟩,
   ⟨275456,5120,![1,10,8,3,9,5]⟩,
   ⟨275456,263168,![1,10,8,5,9,3]⟩,
   ⟨2109440,4096,![1,10,8,3,7,9]⟩,
   ⟨134528,1024,![1,2,3,5,6,7]⟩,
   ⟨2432,2048,![1,2,10,3,6,7]⟩,
   ⟨131456,128,![1,2,10,6,5,7]⟩,
   ⟨2237696,2229248,![1,2,3,5,7,9]⟩,
   ⟨2105600,2097408,![1,2,10,3,7,9]⟩,
   ⟨9216,9216,![1,2,10,3,5,9]⟩]

private def covered34_0 : Cover 11 :=
  .split 10
    (.split 18
      (.split 12
        (.other 0)
        (.split 17
          (.split 15
            (.other 1)
            (.other 2))
          (.other 3)))
      (.split 9
        (.other 4)
        (.split 13
          (.split 12
            (.other 5)
            (.other 6))
          (.split 12
            (.other 7)
            (.split 17
              (.other 8)
              (.split 8
                (.split 21
                  (.split 15
                    (.other 9)
                    (.split 16
                      (.other 10)
                      (.split 6
                        (.other 11)
                        (.split 4
                          (.other 12)
                          (.split 1
                            (.other 13)
                            (.split 7
                              (.split 11
                                (.split 20
                                  (.split 14
                                    (.other 14)
                                    (.split 19
                                      (.other 15)
                                      (.split 5
                                        (.split 0
                                          (.other 16)
                                          (.split 3
                                            (.split 2
                                              (.other 1045119)
                                              (.other 17))
                                            (.other 18)))
                                        (.split 3
                                          (.split 2
                                            (.split 0
                                              (.other 1045150)
                                              (.other 1045151))
                                            (.other 19))
                                          (.other 20)))))
                                  (.other 21))
                                (.other 22))
                              (.split 20
                                (.split 11
                                  (.other 23)
                                  (.split 3
                                    (.split 5
                                      (.split 2
                                        (.split 0
                                          (.other 24)
                                          (.split 19
                                            (.other 25)
                                            (.split 14
                                              (.other 26)
                                              (.other 1047295))))
                                        (.other 27))
                                      (.other 28))
                                    (.other 29)))
                                (.other 30))))))))
                  (.other 31))
                (.other 32)))))))
    (.split 13
      (.split 18
        (.split 12
          (.split 9
            (.other 33)
            (.other 34))
          (.other 35))
        (.split 12
          (.other 36)
          (.split 21
            (.other 37)
            (.split 8
              (.split 17
                (.split 7
                  (.split 11
                    (.other 38)
                    (.other 39))
                  (.other 40))
                (.other 41))
              (.other 42)))))
      (.other 43))

private def clauses34_1 : List (TreeClause 11) :=
  [⟨6400,0,![1,2,10,4,8,7]⟩,
   ⟨2305,256,![0,1,2,7,10,4]⟩,
   ⟨36873,1,![0,2,3,4,10,8]⟩,
   ⟨38921,32769,![0,2,3,4,8,7]⟩,
   ⟨6153,9,![0,2,8,7,10,4]⟩,
   ⟨2103296,4096,![2,8,7,9,10,4]⟩,
   ⟨266240,4096,![2,8,9,10,4,5]⟩,
   ⟨25600,0,![2,3,4,5,10,6]⟩,
   ⟨531456,4096,![2,8,7,10,6,4]⟩,
   ⟨1577984,528384,![2,8,6,9,10,4]⟩,
   ⟨266816,266240,![1,2,8,5,9,4]⟩,
   ⟨1050304,1048640,![1,2,5,4,6,9]⟩,
   ⟨3456,128,![1,2,6,10,7,4]⟩,
   ⟨2099968,2097664,![1,2,9,10,7,4]⟩,
   ⟨1139735,1056769,![0,2,3,5,6,9]⟩,
   ⟨1049623,1048579,![0,2,5,4,6,9]⟩,
   ⟨1131541,1048593,![0,2,9,3,6,4]⟩,
   ⟨19461,5,![0,2,6,3,7,4]⟩,
   ⟨19456,16384,![2,3,4,6,10,7]⟩,
   ⟨134144,1024,![2,6,5,7,4,10]⟩,
   ⟨2304000,2228224,![2,3,4,5,7,9]⟩,
   ⟨3230720,2098176,![2,3,6,4,7,9]⟩,
   ⟨3227648,2113536,![3,4,6,10,7,9]⟩,
   ⟨1049600,1049600,![2,6,5,9,4,10]⟩,
   ⟨2164736,2162688,![2,3,4,9,10,7]⟩,
   ⟨2305,2048,![0,1,2,10,7,4]⟩,
   ⟨288,256,![0,1,7,10,4,3]⟩,
   ⟨536,0,![0,1,10,4,8,9]⟩,
   ⟨6153,2056,![0,8,7,10,2,4]⟩,
   ⟨4121,4104,![0,8,2,9,10,4]⟩,
   ⟨529,512,![0,1,2,9,10,4]⟩,
   ⟨2103296,2048,![2,7,8,9,10,4]⟩,
   ⟨2163504,304,![0,1,9,3,7,4]⟩,
   ⟨4121,4112,![0,9,8,2,10,4]⟩,
   ⟨32776,8,![0,8,7,10,4,3]⟩,
   ⟨576,512,![1,2,9,10,4,5]⟩,
   ⟨388,256,![0,1,7,10,6,4]⟩,
   ⟨1157,128,![0,1,2,6,10,4]⟩,
   ⟨529421,5128,![0,8,2,10,6,4]⟩,
   ⟨139618,352,![0,1,3,5,7,10]⟩,
   ⟨1049623,1049616,![0,9,6,2,5,4]⟩,
   ⟨1031,1026,![0,5,4,6,10,2]⟩,
   ⟨19461,2052,![0,6,7,2,3,4]⟩,
   ⟨17413,1028,![0,6,2,3,4,10]⟩,
   ⟨16388,16388,![0,6,3,7,4,10]⟩,
   ⟨2164753,2099216,![0,9,7,2,3,4]⟩,
   ⟨65553,65552,![0,9,3,2,4,10]⟩,
   ⟨2049,2049,![0,2,3,7,4,10]⟩]

private def covered34_1 : Cover 11 :=
  .split 11
    (.split 12
      (.split 8
        (.other 0)
        (.split 0
          (.other 1)
          (.split 3
            (.split 15
              (.other 2)
              (.other 3))
            (.other 4))))
      (.split 21
        (.other 5)
        (.split 16
          (.split 18
            (.other 6)
            (.split 10
              (.split 14
                (.split 13
                  (.other 7)
                  (.split 19
                    (.other 8)
                    (.split 20
                      (.other 9)
                      (.split 0
                        (.split 8
                          (.split 9
                            (.split 7
                              (.split 6
                                (.other 10)
                                (.other 11))
                              (.other 12))
                            (.other 13))
                          (.other 1))
                        (.split 2
                          (.split 4
                            (.split 1
                              (.other 14)
                              (.other 15))
                            (.other 16))
                          (.other 17))))))
                (.other 18))
              (.split 17
                (.other 19)
                (.split 13
                  (.other 20)
                  (.split 20
                    (.split 14
                      (.other 21)
                      (.other 22))
                    (.other 23))))))
          (.other 24))))
    (.split 0
      (.split 8
        (.other 25)
        (.split 5
          (.other 26)
          (.split 4
            (.split 9
              (.split 3
                (.other 27)
                (.split 12
                  (.other 28)
                  (.other 29)))
              (.other 30))
            (.split 16
              (.split 21
                (.split 12
                  (.other 31)
                  (.split 9
                    (.other 32)
                    (.split 3
                      (.other 33)
                      (.split 15
                        (.other 34)
                        (.split 18
                          (.other 6)
                          (.split 6
                            (.other 35)
                            (.split 2
                              (.split 7
                                (.other 36)
                                (.split 10
                                  (.other 37)
                                  (.split 1
                                    (.split 20
                                      (.split 19
                                        (.other 38)
                                        (.split 13
                                          (.split 17
                                            (.other 39)
                                            (.split 14
                                              (.other 958504)
                                              (.other 974888)))
                                          (.split 14
                                            (.split 17
                                              (.other 835624)
                                              (.other 966696))
                                            (.split 17
                                              (.other 852008)
                                              (.other 983080)))))
                                      (.other 40))
                                    (.other 41))))
                              (.split 14
                                (.split 10
                                  (.other 42)
                                  (.other 43))
                                (.other 44)))))))))
                (.other 45))
              (.other 46)))))
      (.other 47))

private def clauses34_2 : List (TreeClause 11) :=
  [⟨9216,0,![2,3,4,5,10,8]⟩,
   ⟨263168,1024,![2,4,5,10,8,9]⟩,
   ⟨8288,0,![1,10,4,8,3,5]⟩,
   ⟨70,0,![0,1,10,4,8,5]⟩,
   ⟨8198,2,![0,4,3,5,10,8]⟩,
   ⟨8292,36,![0,1,5,3,10,8]⟩,
   ⟨8288,64,![1,2,5,10,3,8]⟩,
   ⟨8292,96,![0,1,3,5,10,8]⟩,
   ⟨8198,4,![0,5,4,3,10,8]⟩,
   ⟨576,64,![1,2,5,10,8,9]⟩,
   ⟨131074,2,![0,4,3,10,8,7]⟩,
   ⟨288,32,![0,1,3,10,8,7]⟩,
   ⟨90112,0,![3,4,5,10,6,8]⟩,
   ⟨81930,65538,![0,4,3,6,10,8]⟩,
   ⟨16552,40,![0,1,6,3,10,8]⟩,
   ⟨2102033,768,![0,1,2,7,9,10]⟩,
   ⟨3201049,2129928,![0,6,7,9,3,2]⟩,
   ⟨1099801,1081352,![0,6,9,3,8,2]⟩,
   ⟨2626368,832,![1,2,5,7,9,10]⟩,
   ⟨40981,32788,![0,5,9,3,8,2]⟩,
   ⟨22537,9,![0,2,6,3,7,8]⟩,
   ⟨22528,2048,![2,3,6,7,8,10]⟩,
   ⟨22537,4104,![0,6,7,2,8,3]⟩,
   ⟨2663264,864,![1,3,5,7,9,10]⟩,
   ⟨2666517,2101268,![0,5,9,7,2,3]⟩,
   ⟨1107968,34816,![2,3,6,9,5,8]⟩,
   ⟨1050624,1050624,![2,6,5,9,8,10]⟩,
   ⟨536581,528388,![0,5,7,2,8,3]⟩,
   ⟨4097,4097,![0,2,3,7,8,10]⟩,
   ⟨548876,16388,![0,5,6,3,7,8]⟩,
   ⟨22528,16384,![2,3,6,7,8,10]⟩,
   ⟨1051289,2560,![0,1,2,9,6,8]⟩,
   ⟨1379355,265218,![0,4,2,9,6,8]⟩,
   ⟨2666517,2654212,![0,5,7,9,3,2]⟩,
   ⟨1050653,2068,![0,5,9,6,8,2]⟩,
   ⟨536581,524293,![0,2,5,3,7,8]⟩,
   ⟨536576,528384,![2,3,7,5,8,10]⟩,
   ⟨16392,16392,![0,6,3,7,8,10]⟩,
   ⟨555008,8192,![2,3,5,6,7,8]⟩,
   ⟨530432,2048,![2,6,5,7,8,10]⟩,
   ⟨536576,532480,![2,3,5,7,8,10]⟩,
   ⟨536576,12288,![2,3,7,5,8,10]⟩,
   ⟨8293,8192,![0,1,2,10,3,5]⟩,
   ⟨8292,8224,![0,1,3,10,5,8]⟩,
   ⟨69,64,![0,1,2,5,10,8]⟩,
   ⟨528389,528388,![0,5,7,2,8,10]⟩,
   ⟨40960,40960,![2,3,5,9,8,10]⟩]

private def covered34_2 : Cover 11 :=
  .split 13
    (.split 10
      (.other 0)
      (.split 18
        (.other 1)
        (.split 6
          (.split 5
            (.other 2)
            (.split 2
              (.split 1
                (.other 3)
                (.other 4))
              (.other 5)))
          (.split 5
            (.other 6)
            (.split 2
              (.other 7)
              (.split 1
                (.other 8)
                (.split 9
                  (.other 9)
                  (.split 17
                    (.other 10)
                    (.split 8
                      (.other 11)
                      (.split 14
                        (.split 16
                          (.other 12)
                          (.split 3
                            (.other 13)
                            (.split 7
                              (.other 14)
                              (.split 12
                                (.split 11
                                  (.split 0
                                    (.split 4
                                      (.split 21
                                        (.other 15)
                                        (.split 20
                                          (.split 15
                                            (.split 19
                                              (.other 2557981)
                                              (.other 3082269))
                                            (.other 16))
                                          (.split 15
                                            (.split 19
                                              (.other 3606557)
                                              (.other 4130845))
                                            (.other 17))))
                                      (.split 15
                                        (.split 19
                                          (.split 21
                                            (.other 18)
                                            (.split 20
                                              (.other 2557997)
                                              (.other 3606573)))
                                          (.split 20
                                            (.split 21
                                              (.other 985133)
                                              (.other 3082285))
                                            (.split 21
                                              (.other 2033709)
                                              (.other 4130861))))
                                        (.other 19)))
                                    (.other 20))
                                  (.other 21))
                                (.split 0
                                  (.split 19
                                    (.split 11
                                      (.other 22)
                                      (.split 20
                                        (.split 15
                                          (.split 21
                                            (.other 23)
                                            (.split 4
                                              (.other 2564125)
                                              (.other 24)))
                                          (.other 25))
                                        (.other 26)))
                                    (.other 27))
                                  (.other 28))))))
                        (.split 3
                          (.split 19
                            (.other 29)
                            (.split 12
                              (.split 0
                                (.split 11
                                  (.other 30)
                                  (.split 20
                                    (.split 4
                                      (.split 21
                                        (.other 15)
                                        (.split 15
                                          (.split 7
                                            (.other 31)
                                            (.split 16
                                              (.other 32)
                                              (.other 3100693)))
                                          (.other 33)))
                                      (.other 34))
                                    (.other 26)))
                                (.other 35))
                              (.other 36)))
                          (.other 37))))))))))))
    (.split 15
      (.split 12
        (.split 19
          (.split 11
            (.split 14
              (.other 38)
              (.other 30))
            (.other 39))
          (.other 40))
        (.split 0
          (.split 19
            (.other 41)
            (.split 2
              (.split 6
                (.split 5
                  (.other 42)
                  (.other 43))
                (.other 44))
              (.other 45)))
          (.other 28)))
      (.other 46))


private def clauses34 (m : Fin 3) : List (TreeClause 11) :=
  ![clauses34_0,clauses34_1,clauses34_2] m

private def covered34 (m : Fin 3) : Cover 11 :=
  ![covered34_0,covered34_1,covered34_2] m

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

private theorem clauses34_valid0 :
    ∀ t : Fin (clauses34 0).length, ((clauses34 0).get t).Valid (family34 0).pattern := by decide

private theorem covered34_valid0 :
    (covered34 0).Valid (family34 0).pattern
      (MaskOrClause (family34 0) (clauses34 0) (residues34 0)) 0 0 := by decide

private theorem clauses34_valid1 :
    ∀ t : Fin (clauses34 1).length, ((clauses34 1).get t).Valid (family34 1).pattern := by decide

private theorem covered34_valid1 :
    (covered34 1).Valid (family34 1).pattern
      (MaskOrClause (family34 1) (clauses34 1) (residues34 1)) 0 0 := by decide

private theorem clauses34_valid2 :
    ∀ t : Fin (clauses34 2).length, ((clauses34 2).get t).Valid (family34 2).pattern := by decide

private theorem covered34_valid2 :
    (covered34 2).Valid (family34 2).pattern
      (MaskOrClause (family34 2) (clauses34 2) (residues34 2)) 0 0 := by decide

private theorem clauses34_valid (m : Fin 3) :
    ∀ i : Fin (clauses34 m).length, ((clauses34 m).get i).Valid (family34 m).pattern := by
  fin_cases m
  · exact clauses34_valid0
  · exact clauses34_valid1
  · exact clauses34_valid2

private theorem covered34_valid (m : Fin 3) :
    (covered34 m).Valid (family34 m).pattern
      (MaskOrClause (family34 m) (clauses34 m) (residues34 m)) 0 0 := by
  fin_cases m
  · exact covered34_valid0
  · exact covered34_valid1
  · exact covered34_valid2

theorem classification34 (m : Fin 3) (row : ℕ) :
    (∃ T, SixTree ((family34 m).pattern.edge row) T) ∨
      ∃ tag ∈ residues34 m, ∀ i j,
        (family34 m).pattern.edge row i j = (family34 m).pattern.edge tag i j :=
  classified_with_full_mask (clauses34_valid m) (covered34_valid m) row

theorem family34_consistent (m : Fin 3) : Consistent layout34 m (family34 m) := by
  fin_cases m <;> decide

def edge34 (m : Fin 3) (tag : ℕ) : Fin 11 → Fin 11 → Bool := (family34 m).pattern.edge tag

#print axioms classification34
#print axioms family34_consistent

end Graffiti199Depleted.WiderOmission
