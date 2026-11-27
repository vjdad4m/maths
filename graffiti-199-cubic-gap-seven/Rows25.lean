import FullMaskCover

namespace Graffiti199Depleted.WiderOmission

open CompactOmission

def layout25 : Layout 10 where
  port := ⟨![1,3,8], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  interior := by decide

def family25 (m : Fin 3) : Family 10 :=
  ![⟨![2,1029,10,1044,40,80,160,320,1664,256,266],[(0,3),(0,4),(0,5),(0,6),(0,8),(0,9),(2,5),(2,6),(2,8),(3,5),(3,6),(3,7),(3,9),(4,6),(4,7),(4,8),(5,7),(5,8),(5,9),(6,8),(6,9),(7,9)]⟩,
    ⟨![2,1029,10,1044,40,80,160,320,1664,256,266],[(0,4),(0,5),(0,6),(0,8),(0,9),(1,4),(1,5),(1,6),(1,7),(1,9),(2,5),(2,6),(2,8),(4,6),(4,7),(4,8),(5,7),(5,8),(5,9),(6,8),(6,9),(7,9)]⟩,
    ⟨![2,1029,10,1044,40,80,160,320,1664,256,266],[(0,3),(0,4),(0,5),(0,6),(0,9),(1,4),(1,5),(1,6),(1,7),(1,9),(2,5),(2,6),(3,5),(3,6),(3,7),(3,9),(4,6),(4,7),(5,7),(5,9),(6,9),(7,9)]⟩] m

def residues25 (m : Fin 3) : List ℕ := ![[786225],[783352,784376,777208,785400,778232,786424],[783359,1831935,521215,1569791,1045503,2094079,2225135,3273711,2749423,3797999,2487279,3535855,3011567,4060143,2356207,3404783,2880495,3929071,2618351,3666927,3142639,4191215,2225151,3273727,2749439,3798015,2487295,3535871,3011583,4060159,2356223,3404799,2880511,3929087,2618367,3666943,3142655,4191231,2619371,2423783,3996647,2621411,2620391]] m

private def clauses25_0 : List (TreeClause 11) :=
  [⟨36864,0,![1,10,3,8,4,9]⟩,
   ⟨37120,4096,![1,2,3,4,9,8]⟩,
   ⟨51456,256,![1,2,3,8,4,7]⟩,
   ⟨18435,2048,![0,1,2,3,4,7]⟩,
   ⟨18435,2049,![0,3,2,4,7,10]⟩,
   ⟨49426,16640,![0,1,2,8,7,4]⟩,
   ⟨49426,16656,![0,8,2,7,10,4]⟩,
   ⟨49426,258,![0,1,4,2,8,7]⟩,
   ⟨49426,274,![0,4,8,2,7,10]⟩,
   ⟨16386,16386,![0,1,4,2,10,7]⟩,
   ⟨33024,32768,![1,2,10,8,4,9]⟩,
   ⟨33074,33024,![0,1,2,8,4,9]⟩,
   ⟨33074,33040,![0,8,2,4,9,10]⟩,
   ⟨2146560,33024,![1,2,8,4,7,9]⟩,
   ⟨33074,33056,![0,9,8,2,4,10]⟩,
   ⟨426304,33024,![1,2,8,4,9,5]⟩,
   ⟨2556224,131328,![1,2,8,5,7,9]⟩,
   ⟨1966528,131328,![1,2,8,5,9,6]⟩,
   ⟨1614208,557312,![1,2,8,4,6,9]⟩,
   ⟨4131,32,![0,1,9,2,3,4]⟩,
   ⟨4131,33,![0,3,9,2,4,10]⟩,
   ⟨4131,4128,![0,9,3,2,4,10]⟩,
   ⟨266816,4096,![1,2,3,4,9,5]⟩,
   ⟨1062016,12288,![1,2,3,4,9,6]⟩,
   ⟨2119680,20480,![1,2,3,4,9,7]⟩,
   ⟨1310956,160,![0,1,9,2,6,5]⟩,
   ⟨1310764,1048608,![0,1,9,10,6,5]⟩,
   ⟨1310764,40,![0,1,6,9,10,5]⟩,
   ⟨204,8,![0,1,6,2,10,5]⟩,
   ⟨1310912,1048704,![1,2,10,6,5,9]⟩,
   ⟨262246,262176,![0,1,9,2,5,4]⟩,
   ⟨70,64,![0,1,2,10,5,4]⟩,
   ⟨262182,36,![0,1,5,9,10,4]⟩,
   ⟨70,4,![0,1,5,2,10,4]⟩,
   ⟨262208,262208,![1,2,10,5,4,9]⟩,
   ⟨2097184,2097184,![0,1,9,2,10,7]⟩,
   ⟨49426,33026,![0,4,8,2,7,10]⟩,
   ⟨8398,2,![0,1,4,2,5,6]⟩,
   ⟨204,4,![0,1,5,2,10,6]⟩,
   ⟨8384,64,![1,2,10,5,4,6]⟩,
   ⟨24714,8194,![0,1,4,2,6,7]⟩,
   ⟨136,128,![0,1,2,10,6,7]⟩,
   ⟨3145768,2097160,![0,1,6,10,7,9]⟩,
   ⟨136,8,![0,1,6,2,10,7]⟩,
   ⟨24586,10,![0,1,4,6,10,7]⟩,
   ⟨24704,8320,![1,2,10,6,4,7]⟩,
   ⟨34,34,![0,1,4,9,2,10]⟩]

private def covered25_0 : Cover 11 :=
  .split 15
    (.split 12
      (.other 0)
      (.split 8
        (.other 1)
        (.split 1
          (.split 14
            (.split 11
              (.other 2)
              (.split 0
                (.other 3)
                (.other 4)))
            (.split 4
              (.other 5)
              (.other 6)))
          (.split 14
            (.split 4
              (.other 7)
              (.other 8))
            (.other 9)))))
    (.split 8
      (.other 10)
      (.split 1
        (.split 5
          (.split 4
            (.other 11)
            (.other 12))
          (.split 21
            (.split 14
              (.other 13)
              (.split 4
                (.other 14)
                (.split 2
                  (.split 6
                    (.split 18
                      (.split 17
                        (.other 15)
                        (.split 16
                          (.other 16)
                          (.split 3
                            (.split 20
                              (.split 7
                                (.split 19
                                  (.other 17)
                                  (.split 13
                                    (.other 18)
                                    (.split 12
                                      (.split 0
                                        (.other 19)
                                        (.other 20))
                                      (.split 0
                                        (.other 21)
                                        (.split 9
                                          (.other 22)
                                          (.split 10
                                            (.other 23)
                                            (.split 11
                                              (.other 24)
                                              (.other 786272))))))))
                                (.other 25))
                              (.other 26))
                            (.split 20
                              (.other 27)
                              (.split 7
                                (.other 28)
                                (.other 29))))))
                      (.other 30))
                    (.other 31))
                  (.split 18
                    (.other 32)
                    (.split 6
                      (.other 33)
                      (.other 34))))))
            (.other 35)))
        (.split 14
          (.split 5
            (.split 21
              (.other 13)
              (.split 4
                (.other 36)
                (.split 3
                  (.split 7
                    (.split 13
                      (.split 6
                        (.split 2
                          (.other 37)
                          (.other 38))
                        (.other 39))
                      (.other 40))
                    (.other 41))
                  (.split 20
                    (.other 42)
                    (.split 7
                      (.other 43)
                      (.split 13
                        (.other 44)
                        (.other 45)))))))
            (.other 46))
          (.other 9))))

private def clauses25_1 : List (TreeClause 11) :=
  [⟨11264,0,![2,3,4,10,5,6]⟩,
   ⟨68608,1024,![2,3,5,10,6,7]⟩,
   ⟨3270,1024,![0,1,2,3,5,6]⟩,
   ⟨198,64,![0,1,5,10,6,3]⟩,
   ⟨2436,256,![0,1,2,7,3,6]⟩,
   ⟨10405,128,![0,1,2,6,3,4]⟩,
   ⟨10405,160,![0,1,2,4,6,10]⟩,
   ⟨3078,1028,![0,6,5,2,3,10]⟩,
   ⟨81923,65537,![0,4,3,5,10,7]⟩,
   ⟨66562,66562,![0,5,2,7,3,10]⟩,
   ⟨26624,8192,![2,3,4,10,6,7]⟩,
   ⟨26624,2048,![2,3,6,4,10,7]⟩,
   ⟨264,0,![0,1,10,3,8,7]⟩,
   ⟨16673,256,![0,1,2,7,3,4]⟩,
   ⟨16673,288,![0,1,2,4,7,10]⟩,
   ⟨49161,8,![0,8,7,10,3,4]⟩,
   ⟨53257,32776,![0,8,4,7,3,2]⟩,
   ⟨53257,36872,![0,8,2,4,7,10]⟩,
   ⟨24581,8193,![0,4,3,6,10,7]⟩,
   ⟨2052,2052,![0,6,2,7,3,10]⟩,
   ⟨2101248,0,![2,3,10,8,7,9]⟩,
   ⟨2150400,20480,![2,8,7,9,10,4]⟩,
   ⟨4632,4096,![0,1,2,3,8,9]⟩,
   ⟨4360,4096,![0,1,2,3,8,7]⟩,
   ⟨2097936,768,![0,1,2,7,9,3]⟩,
   ⟨2101272,4104,![0,8,2,7,9,3]⟩,
   ⟨2101272,4112,![0,9,8,2,7,3]⟩,
   ⟨524300,8,![0,8,7,10,6,3]⟩,
   ⟨655374,524296,![0,8,6,10,5,3]⟩,
   ⟨196618,131080,![0,8,5,7,10,3]⟩,
   ⟨16673,16384,![0,1,2,3,4,7]⟩,
   ⟨16673,16416,![0,1,2,4,10,7]⟩,
   ⟨2097936,272,![0,1,9,2,7,3]⟩,
   ⟨65858,65792,![0,1,7,10,5,3]⟩,
   ⟨16673,16640,![0,1,2,7,10,4]⟩,
   ⟨1058837,1056784,![0,9,6,4,3,2]⟩,
   ⟨3147796,1050640,![0,9,6,2,7,3]⟩,
   ⟨26629,16388,![0,6,7,4,3,2]⟩,
   ⟨10245,8196,![0,6,4,3,2,10]⟩,
   ⟨262163,262160,![0,9,5,4,3,10]⟩,
   ⟨1027,2,![0,5,4,3,2,10]⟩,
   ⟨81923,16386,![0,5,4,3,7,10]⟩,
   ⟨16385,16385,![0,4,3,7,2,10]⟩,
   ⟨2113536,2113536,![2,3,4,10,7,9]⟩]

private def covered25_1 : Cover 11 :=
  .split 14
    (.split 11
      (.split 13
        (.split 10
          (.other 0)
          (.split 16
            (.other 1)
            (.split 1
              (.split 0
                (.split 2
                  (.split 7
                    (.split 8
                      (.split 6
                        (.other 2)
                        (.other 3))
                      (.other 4))
                    (.split 5
                      (.other 5)
                      (.other 6)))
                  (.other 7))
                (.other 8))
              (.other 9))))
        (.other 10))
      (.split 2
        (.split 13
          (.other 11)
          (.split 0
            (.split 3
              (.split 8
                (.other 12)
                (.split 5
                  (.other 13)
                  (.other 14)))
              (.split 15
                (.other 15)
                (.split 12
                  (.other 16)
                  (.other 17))))
            (.other 18)))
        (.other 19)))
    (.split 21
      (.split 12
        (.other 20)
        (.split 0
          (.split 15
            (.other 21)
            (.split 4
              (.split 3
                (.split 9
                  (.other 22)
                  (.split 8
                    (.other 23)
                    (.other 24)))
                (.other 25))
              (.split 3
                (.other 26)
                (.split 1
                  (.split 18
                    (.split 2
                      (.split 19
                        (.other 27)
                        (.split 17
                          (.other 28)
                          (.split 16
                            (.other 29)
                            (.split 8
                              (.split 5
                                (.other 30)
                                (.other 31))
                              (.split 9
                                (.other 32)
                                (.split 6
                                  (.other 33)
                                  (.split 7
                                    (.other 3)
                                    (.split 5
                                      (.other 34)
                                      (.split 11
                                        (.split 13
                                          (.other 6)
                                          (.split 20
                                            (.split 10
                                              (.other 783396)
                                              (.other 784420))
                                            (.other 35)))
                                        (.split 20
                                          (.split 10
                                            (.split 13
                                              (.other 777252)
                                              (.other 785444))
                                            (.split 13
                                              (.other 778276)
                                              (.other 786468)))
                                          (.other 36)))))))))))
                      (.split 11
                        (.split 13
                          (.other 37)
                          (.other 38))
                        (.other 19)))
                    (.other 39))
                  (.split 10
                    (.other 40)
                    (.split 16
                      (.other 41)
                      (.other 9)))))))
          (.other 42)))
      (.other 43))

private def clauses25_2 : List (TreeClause 11) :=
  [⟨256,0,![0,1,2,10,8,7]⟩,
   ⟨32768,0,![2,3,4,10,8,9]⟩,
   ⟨35,0,![0,1,10,3,8,4]⟩,
   ⟨3,1,![0,3,2,4,10,8]⟩,
   ⟨34,32,![0,1,2,4,10,8]⟩,
   ⟨34,2,![0,1,4,2,10,8]⟩,
   ⟨3,2,![0,4,3,2,10,8]⟩,
   ⟨16385,1,![0,3,2,10,8,7]⟩,
   ⟨544,32,![1,2,4,10,8,9]⟩,
   ⟨1120,32,![1,2,4,10,5,8]⟩,
   ⟨5120,0,![2,3,4,10,5,8]⟩,
   ⟨3264,64,![1,2,5,10,6,8]⟩,
   ⟨15360,4096,![2,3,5,10,6,8]⟩,
   ⟨1092,64,![0,1,2,5,10,8]⟩,
   ⟨67744,160,![1,2,4,6,10,8]⟩,
   ⟨2184,128,![0,1,2,6,10,8]⟩,
   ⟨2097936,768,![0,1,2,7,9,10]⟩,
   ⟨2229024,800,![1,2,4,7,9,10]⟩,
   ⟨2885440,832,![1,2,5,7,9,10]⟩,
   ⟨265216,1024,![2,5,6,7,8,10]⟩,
   ⟨394246,263170,![0,4,5,2,7,8]⟩,
   ⟨525908,1536,![0,1,2,9,5,8]⟩,
   ⟨562197,33793,![0,3,2,9,5,8]⟩,
   ⟨2440,256,![0,1,2,7,6,8]⟩,
   ⟨1051288,640,![0,1,2,6,9,8]⟩,
   ⟨1051288,520,![0,1,6,2,9,8]⟩,
   ⟨1091609,32777,![0,3,6,2,9,8]⟩,
   ⟨1116832,672,![1,2,4,6,9,8]⟩,
   ⟨1575936,1049600,![2,5,6,9,8,10]⟩,
   ⟨525334,1042,![0,4,9,5,8,2]⟩,
   ⟨263172,263172,![0,5,2,7,8,10]⟩,
   ⟨525312,525312,![2,5,4,9,8,10]⟩,
   ⟨2184,2048,![0,1,2,10,6,8]⟩,
   ⟨10249,2049,![0,3,2,10,6,8]⟩,
   ⟨458752,0,![4,5,6,7,8,10]⟩,
   ⟨393222,262146,![0,4,5,7,8,10]⟩,
   ⟨1092,4,![0,1,5,2,10,8]⟩,
   ⟨5125,5,![0,3,5,2,10,8]⟩,
   ⟨3344410,2099218,![0,4,9,7,6,2]⟩,
   ⟨1641472,526336,![2,6,5,4,9,8]⟩,
   ⟨1575964,1050628,![0,5,6,2,9,8]⟩,
   ⟨1116186,1050642,![0,4,9,6,8,2]⟩,
   ⟨394240,263168,![2,5,4,7,8,10]⟩,
   ⟨198666,133122,![0,4,7,6,8,2]⟩,
   ⟨198666,67586,![0,4,6,2,7,8]⟩,
   ⟨1573596,640,![0,1,6,9,5,8]⟩,
   ⟨525908,576,![0,1,2,5,9,8]⟩,
   ⟨394246,132098,![0,4,5,7,2,8]⟩,
   ⟨524310,524290,![0,4,5,9,8,10]⟩,
   ⟨262156,4,![0,5,6,7,8,10]⟩,
   ⟨525908,516,![0,1,5,2,9,8]⟩,
   ⟨562197,32773,![0,3,5,2,9,8]⟩,
   ⟨1572892,524292,![0,5,6,9,8,10]⟩,
   ⟨1116186,67602,![0,4,9,6,8,2]⟩,
   ⟨1116160,1116160,![2,6,4,9,8,10]⟩,
   ⟨2056,2056,![0,6,2,7,8,10]⟩]

private def covered25_2 : Cover 11 :=
  .split 8
    (.other 0)
    (.split 15
      (.other 1)
      (.split 1
        (.split 5
          (.split 0
            (.other 2)
            (.other 3))
          (.other 4))
        (.split 5
          (.other 5)
          (.split 0
            (.other 6)
            (.split 14
              (.other 7)
              (.split 9
                (.other 8)
                (.split 11
                  (.split 10
                    (.split 6
                      (.other 9)
                      (.split 12
                        (.other 10)
                        (.split 7
                          (.other 11)
                          (.split 13
                            (.other 12)
                            (.split 2
                              (.other 13)
                              (.split 16
                                (.other 14)
                                (.split 3
                                  (.other 15)
                                  (.split 21
                                    (.split 4
                                      (.other 16)
                                      (.split 17
                                        (.other 17)
                                        (.split 18
                                          (.split 19
                                            (.other 18)
                                            (.split 20
                                              (.other 783415)
                                              (.other 1831991)))
                                          (.split 19
                                            (.split 20
                                              (.other 521271)
                                              (.other 1569847))
                                            (.split 20
                                              (.other 1045559)
                                              (.other 2094135))))))
                                    (.split 4
                                      (.split 17
                                        (.split 18
                                          (.split 19
                                            (.split 20
                                              (.other 2225191)
                                              (.other 3273767))
                                            (.split 20
                                              (.other 2749479)
                                              (.other 3798055)))
                                          (.split 19
                                            (.split 20
                                              (.other 2487335)
                                              (.other 3535911))
                                            (.split 20
                                              (.other 3011623)
                                              (.other 4060199))))
                                        (.split 18
                                          (.split 19
                                            (.split 20
                                              (.other 2356263)
                                              (.other 3404839))
                                            (.split 20
                                              (.other 2880551)
                                              (.other 3929127)))
                                          (.split 19
                                            (.split 20
                                              (.other 2618407)
                                              (.other 3666983))
                                            (.split 20
                                              (.other 3142695)
                                              (.other 4191271)))))
                                      (.split 17
                                        (.split 18
                                          (.split 19
                                            (.split 20
                                              (.other 2225207)
                                              (.other 3273783))
                                            (.split 20
                                              (.other 2749495)
                                              (.other 3798071)))
                                          (.split 19
                                            (.split 20
                                              (.other 2487351)
                                              (.other 3535927))
                                            (.split 20
                                              (.other 3011639)
                                              (.other 4060215))))
                                        (.split 18
                                          (.split 19
                                            (.split 20
                                              (.other 2356279)
                                              (.other 3404855))
                                            (.split 20
                                              (.other 2880567)
                                              (.other 3929143)))
                                          (.split 19
                                            (.split 20
                                              (.other 2618423)
                                              (.other 3666999))
                                            (.split 20
                                              (.other 3142711)
                                              (.other 4191287))))))))))))))
                    (.split 19
                      (.split 18
                        (.other 19)
                        (.split 2
                          (.split 4
                            (.split 21
                              (.other 16)
                              (.split 20
                                (.split 17
                                  (.other 20)
                                  (.split 6
                                    (.other 21)
                                    (.split 12
                                      (.other 22)
                                      (.split 3
                                        (.split 7
                                          (.other 23)
                                          (.other 24))
                                        (.split 7
                                          (.other 25)
                                          (.split 13
                                            (.other 26)
                                            (.split 16
                                              (.other 27)
                                              (.other 2619427))))))))
                                (.other 28)))
                            (.other 29))
                          (.other 30)))
                      (.other 31)))
                  (.split 3
                    (.split 7
                      (.other 32)
                      (.split 13
                        (.other 33)
                        (.split 16
                          (.split 17
                            (.split 18
                              (.other 34)
                              (.split 10
                                (.split 2
                                  (.other 35)
                                  (.split 21
                                    (.other 17)
                                    (.split 6
                                      (.other 36)
                                      (.split 12
                                        (.other 37)
                                        (.split 20
                                          (.split 19
                                            (.split 4
                                              (.other 2423839)
                                              (.other 38))
                                            (.other 39))
                                          (.split 4
                                            (.split 19
                                              (.other 40)
                                              (.other 3996703))
                                            (.other 41)))))))
                                (.other 42)))
                            (.other 43))
                          (.split 20
                            (.split 4
                              (.split 17
                                (.other 44)
                                (.split 21
                                  (.other 16)
                                  (.split 2
                                    (.split 19
                                      (.split 6
                                        (.other 45)
                                        (.split 10
                                          (.other 46)
                                          (.split 12
                                            (.other 22)
                                            (.split 18
                                              (.other 47)
                                              (.other 2621467)))))
                                      (.other 48))
                                    (.split 19
                                      (.split 18
                                        (.other 49)
                                        (.split 10
                                          (.split 6
                                            (.other 50)
                                            (.split 12
                                              (.other 51)
                                              (.other 2620447)))
                                          (.other 30)))
                                      (.other 52)))))
                              (.other 53))
                            (.other 54)))))
                    (.other 55)))))))))


private def clauses25 (m : Fin 3) : List (TreeClause 11) :=
  ![clauses25_0,clauses25_1,clauses25_2] m

private def covered25 (m : Fin 3) : Cover 11 :=
  ![covered25_0,covered25_1,covered25_2] m

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

private theorem clauses25_valid0 :
    ∀ t : Fin (clauses25 0).length, ((clauses25 0).get t).Valid (family25 0).pattern := by decide

private theorem covered25_valid0 :
    (covered25 0).Valid (family25 0).pattern
      (MaskOrClause (family25 0) (clauses25 0) (residues25 0)) 0 0 := by decide

private theorem clauses25_valid1 :
    ∀ t : Fin (clauses25 1).length, ((clauses25 1).get t).Valid (family25 1).pattern := by decide

private theorem covered25_valid1 :
    (covered25 1).Valid (family25 1).pattern
      (MaskOrClause (family25 1) (clauses25 1) (residues25 1)) 0 0 := by decide

private theorem clauses25_valid2 :
    ∀ t : Fin (clauses25 2).length, ((clauses25 2).get t).Valid (family25 2).pattern := by decide

private theorem covered25_valid2 :
    (covered25 2).Valid (family25 2).pattern
      (MaskOrClause (family25 2) (clauses25 2) (residues25 2)) 0 0 := by decide

private theorem clauses25_valid (m : Fin 3) :
    ∀ i : Fin (clauses25 m).length, ((clauses25 m).get i).Valid (family25 m).pattern := by
  fin_cases m
  · exact clauses25_valid0
  · exact clauses25_valid1
  · exact clauses25_valid2

private theorem covered25_valid (m : Fin 3) :
    (covered25 m).Valid (family25 m).pattern
      (MaskOrClause (family25 m) (clauses25 m) (residues25 m)) 0 0 := by
  fin_cases m
  · exact covered25_valid0
  · exact covered25_valid1
  · exact covered25_valid2

theorem classification25 (m : Fin 3) (row : ℕ) :
    (∃ T, SixTree ((family25 m).pattern.edge row) T) ∨
      ∃ tag ∈ residues25 m, ∀ i j,
        (family25 m).pattern.edge row i j = (family25 m).pattern.edge tag i j :=
  classified_with_full_mask (clauses25_valid m) (covered25_valid m) row

theorem family25_consistent (m : Fin 3) : Consistent layout25 m (family25 m) := by
  fin_cases m <;> decide

def edge25 (m : Fin 3) (tag : ℕ) : Fin 11 → Fin 11 → Bool := (family25 m).pattern.edge tag

#print axioms classification25
#print axioms family25_consistent

end Graffiti199Depleted.WiderOmission
