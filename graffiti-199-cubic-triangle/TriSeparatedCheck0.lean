import TriSeparated

namespace Graffiti199Depleted.WiderOmission
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

private def routes : List (List (SegmentToken 9 2)) :=
  [[.vertex 0,.vertex 1,.across 0 false,.vertex 4,.vertex 9,.vertex 7,.across 1 false,.vertex 8],
   [.vertex 0,.vertex 1,.vertex 9,.vertex 7,.across 0 false,.vertex 4,.across 1 false,.vertex 8],
   [.vertex 0,.across 1 false,.vertex 4,.across 0 true,.vertex 1,.vertex 9,.vertex 7,.vertex 8],
   [.vertex 0,.vertex 1,.vertex 9,.vertex 4,.across 0 true,.across 1 true,.vertex 7,.vertex 8],
   [.vertex 0,.vertex 1,.vertex 9,.vertex 4,.vertex 7,.across 0 false,.across 1 false,.vertex 8],
   [.vertex 0,.vertex 1,.vertex 9,.vertex 4,.across 0 false,.across 1 false,.vertex 7,.vertex 8],
   [.vertex 0,.vertex 1,.across 0 false,.across 1 false,.vertex 7,.vertex 9,.vertex 4,.vertex 8],
   [.vertex 0,.vertex 4,.vertex 9,.vertex 1,.across 0 false,.across 1 false,.vertex 7,.vertex 8],
   [.vertex 0,.vertex 1,.across 0 false,.across 1 false,.vertex 4,.vertex 9,.vertex 7,.vertex 8],
   [.vertex 0,.vertex 7,.across 1 true,.vertex 4,.vertex 9,.vertex 1,.across 0 false,.vertex 8],
   [.vertex 0,.vertex 1,.across 0 false,.vertex 7,.vertex 9,.vertex 4,.across 1 false,.vertex 8]]

private def cover : Cover 10 :=
  (.split 10
  (.split 11
    (.split 9
      (.split 13
        (.split 12
          (.split 14
            (.split 5
              (.split 6
                (.tree ![1,2,9,4,3,5])
                (.split 7
                  (.split 8
                    (.tree ![1,2,4,3,7,6])
                    (.split 1
                      (.split 2
                        (.tree ![0,1,9,4,3,5])
                        (.split 4
                          (.split 3
                            (.split 15
                              (.tree ![0,1,5,4,3,7])
                              (.split 16
                                (.tree ![0,1,5,7,6,8])
                                (.other 0)))
                            (.tree ![0,1,7,4,6,3]))
                          (.tree ![0,1,5,8,4,3])))
                      (.split 3
                        (.tree ![0,1,4,3,7,6])
                        (.split 16
                          (.split 15
                            (.tree ![3,4,5,7,6,8])
                            (.tree ![1,2,7,5,6,8]))
                          (.other 1)))))
                  (.tree ![1,2,4,6,3,5])))
              (.split 8
                (.tree ![1,2,9,3,7,8])
                (.split 15
                  (.split 16
                    (.tree ![3,4,5,7,6,8])
                    (.other 1))
                  (.tree ![1,2,3,7,5,8]))))
            (.tree ![1,9,4,3,5,6]))
          (.split 16
            (.split 1
              (.tree ![0,1,9,4,3,6])
              (.split 4
                (.split 3
                  (.tree ![0,1,4,3,7,8])
                  (.split 14
                    (.tree ![1,9,4,3,5,6])
                    (.split 15
                      (.tree ![1,9,7,6,8,5])
                      (.split 8
                        (.tree ![1,2,9,7,5,8])
                        (.split 5
                          (.split 6
                            (.tree ![1,2,7,4,8,3])
                            (.split 0
                              (.split 2
                                (.tree ![0,4,2,3,5,9])
                                (.other 2))
                              (.split 2
                                (.split 7
                                  (.other 53590)
                                  (.other 3))
                                (.other 2))))
                          (.tree ![1,2,3,7,5,8]))))))
                (.tree ![0,1,4,8,3,6])))
            (.tree ![1,9,4,3,6,8])))
        (.tree ![1,9,4,3,5,8]))
      (.split 15
        (.split 14
          (.split 2
            (.split 12
              (.split 1
                (.split 3
                  (.split 13
                    (.split 4
                      (.split 16
                        (.tree ![0,1,9,7,6,8])
                        (.split 6
                          (.split 8
                            (.split 5
                              (.split 7
                                (.split 0
                                  (.tree ![0,1,2,9,4,3])
                                  (.other 66060))
                                (.tree ![1,2,6,7,4,3]))
                              (.tree ![1,2,3,4,7,8]))
                            (.other 4))
                          (.other 5)))
                      (.tree ![0,1,8,7,4,3]))
                    (.other 6))
                  (.tree ![0,1,7,4,6,3]))
                (.other 7))
              (.other 8))
            (.split 3
              (.tree ![0,1,5,9,3,7])
              (.tree ![0,1,5,7,3,6])))
          (.tree ![1,9,7,6,5,3]))
        (.tree ![1,9,7,5,8,3])))
    (.split 16
      (.tree ![1,9,7,6,8,3])
      (.split 4
        (.split 3
          (.tree ![0,1,9,7,8,3])
          (.other 9))
        (.tree ![0,1,8,9,3,6]))))
  (.split 3
    (.tree ![0,1,9,7,3,6])
    (.split 11
      (.split 16
        (.tree ![1,9,7,3,6,8])
        (.other 10))
      (.other 9))))

theorem validTriSeparated0 :
    cover.Valid (familyTriSeparated 0).pattern
      (RootRouteCheck seamsTriSeparated (familyTriSeparated 0) routes [53579,66049]) 0 0 := by
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
