import TriSeparated

namespace Graffiti199Depleted.WiderOmission
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

private def routes : List (List (SegmentToken 9 2)) :=
  [[.vertex 0,.vertex 1,.across 0 false,.across 1 false,.vertex 7,.vertex 9,.vertex 4,.vertex 8],
   [.vertex 0,.vertex 1,.across 0 false,.across 1 false,.vertex 4,.vertex 9,.vertex 7,.vertex 8],
   [.vertex 0,.vertex 1,.across 0 true,.across 1 true,.vertex 4,.vertex 9,.vertex 7,.vertex 8],
   [.vertex 0,.vertex 1,.vertex 9,.vertex 7,.across 1 true,.vertex 4,.across 0 false,.vertex 8],
   [.vertex 0,.across 0 false,.vertex 4,.across 1 false,.vertex 1,.vertex 9,.vertex 7,.vertex 8],
   [.vertex 0,.across 0 false,.vertex 1,.vertex 9,.vertex 4,.across 1 false,.vertex 7,.vertex 8],
   [.vertex 0,.across 0 false,.vertex 4,.across 1 false,.vertex 7,.vertex 9,.vertex 1,.vertex 8],
   [.vertex 0,.across 0 false,.vertex 4,.vertex 9,.vertex 1,.across 1 false,.vertex 7,.vertex 8],
   [.vertex 0,.across 1 false,.vertex 4,.across 0 true,.vertex 1,.vertex 9,.vertex 7,.vertex 8]]

private def cover : Cover 10 :=
  (.split 1
  (.split 2
    (.split 0
      (.split 5
        (.split 4
          (.split 8
            (.split 3
              (.split 7
                (.tree ![0,1,2,9,7,8])
                (.split 12
                  (.split 14
                    (.tree ![0,1,4,8,3,7])
                    (.split 6
                      (.split 10
                        (.tree ![0,1,2,9,7,6])
                        (.split 15
                          (.split 13
                            (.split 9
                              (.tree ![0,1,2,4,6,3])
                              (.split 11
                                (.tree ![2,4,6,3,5,7])
                                (.other 0)))
                            (.tree ![0,1,4,3,6,7]))
                          (.tree ![0,1,2,6,5,7])))
                      (.split 13
                        (.tree ![0,1,4,6,3,7])
                        (.split 11
                          (.split 9
                            (.tree ![0,1,2,4,3,5])
                            (.tree ![2,4,3,5,8,7]))
                          (.other 1)))))
                  (.tree ![0,1,2,8,3,7])))
              (.split 14
                (.tree ![0,8,7,9,4,5])
                (.split 9
                  (.split 11
                    (.tree ![0,1,2,4,3,5])
                    (.other 0))
                  (.tree ![0,8,4,7,2,5]))))
            (.tree ![0,1,2,9,3,7]))
          (.split 11
            (.split 6
              (.tree ![0,1,3,9,7,6])
              (.split 15
                (.split 13
                  (.tree ![0,1,4,6,5,7])
                  (.split 8
                    (.tree ![0,1,2,3,9,7])
                    (.split 9
                      (.tree ![2,3,4,5,9,7])
                      (.split 14
                        (.tree ![2,4,5,9,7,8])
                        (.split 3
                          (.split 7
                            (.tree ![0,1,4,5,8,7])
                            (.split 16
                              (.split 10
                                (.tree ![0,1,2,6,8,9])
                                (.other 2))
                              (.split 10
                                (.split 12
                                  (.other 91097)
                                  (.other 3))
                                (.other 2))))
                          (.tree ![0,8,4,7,2,5]))))))
                (.tree ![0,1,3,6,5,7])))
            (.tree ![0,1,3,9,5,7])))
        (.tree ![0,1,2,5,9,7]))
      (.split 9
        (.split 8
          (.split 3
            (.split 5
              (.split 7
                (.split 14
                  (.split 4
                    (.split 12
                      (.split 11
                        (.tree ![3,4,5,9,7,8])
                        (.split 6
                          (.split 13
                            (.split 10
                              (.split 15
                                (.split 16
                                  (.tree ![0,1,9,7,6,8])
                                  (.other 67594))
                                (.tree ![0,1,4,5,6,7]))
                              (.tree ![1,2,4,6,3,7]))
                            (.other 1))
                          (.other 4)))
                      (.tree ![0,1,4,3,8,7]))
                    (.other 5))
                  (.tree ![0,1,4,5,8,7]))
                (.other 6))
              (.other 7))
            (.split 14
              (.tree ![0,2,8,7,9,4])
              (.tree ![0,2,8,4,7,5])))
          (.tree ![0,2,3,4,9,7]))
        (.tree ![0,2,4,5,9,7])))
    (.split 11
      (.tree ![0,5,4,3,9,7])
      (.split 15
        (.split 13
          (.tree ![0,5,4,9,7,6])
          (.other 1))
        (.tree ![0,5,3,6,7,9]))))
  (.split 13
    (.tree ![0,4,3,9,7,6])
    (.split 2
      (.split 11
        (.tree ![0,4,3,5,9,7])
        (.other 1))
      (.other 8))))

theorem validTriSeparated2 :
    cover.Valid (familyTriSeparated 2).pattern
      (RootRouteCheck seamsTriSeparated (familyTriSeparated 2) routes [91088,67585]) 0 0 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · refine ⟨by decide +kernel, ?_, ?_⟩
      · decide +kernel
      · decide +kernel
    · refine ⟨by decide +kernel, ?_, ?_⟩
      · decide +kernel
      · decide +kernel
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · refine ⟨by decide +kernel, ?_, ?_⟩
      · decide +kernel
      · decide +kernel

end Graffiti199Depleted.WiderOmission
