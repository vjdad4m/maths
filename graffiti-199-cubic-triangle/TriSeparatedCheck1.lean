import TriSeparated

namespace Graffiti199Depleted.WiderOmission
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

private def routes : List (List (SegmentToken 9 2)) :=
  [[.vertex 0,.vertex 1,.across 0 false,.vertex 4,.vertex 9,.vertex 7,.across 1 false,.vertex 8],
   [.vertex 0,.vertex 1,.across 0 true,.across 1 true,.vertex 4,.vertex 9,.vertex 7,.vertex 8],
   [.vertex 0,.vertex 1,.across 0 false,.vertex 7,.vertex 9,.vertex 4,.across 1 false,.vertex 8],
   [.vertex 0,.across 0 false,.vertex 1,.vertex 7,.vertex 9,.vertex 4,.across 1 false,.vertex 8],
   [.vertex 0,.across 0 false,.vertex 4,.across 1 false,.vertex 1,.vertex 9,.vertex 7,.vertex 8],
   [.vertex 0,.across 0 false,.vertex 4,.vertex 9,.vertex 1,.across 1 false,.vertex 7,.vertex 8],
   [.vertex 0,.across 0 false,.vertex 4,.across 1 false,.vertex 7,.vertex 9,.vertex 1,.vertex 8],
   [.vertex 0,.across 1 false,.vertex 7,.vertex 9,.vertex 4,.across 0 true,.vertex 1,.vertex 8],
   [.vertex 0,.vertex 7,.across 1 true,.vertex 4,.vertex 9,.vertex 1,.across 0 false,.vertex 8],
   [.vertex 0,.vertex 1,.across 1 false,.across 0 false,.vertex 4,.vertex 9,.vertex 7,.vertex 8],
   [.vertex 0,.vertex 1,.vertex 9,.vertex 4,.across 0 true,.across 1 true,.vertex 7,.vertex 8],
   [.vertex 0,.vertex 1,.vertex 9,.vertex 4,.across 1 false,.across 0 false,.vertex 7,.vertex 8]]

private def cover : Cover 10 :=
  (.split 2
  (.split 3
    (.split 0
      (.split 7
        (.split 6
          (.split 9
            (.split 1
              (.split 5
                (.tree ![0,1,2,9,4,5])
                (.split 14
                  (.split 15
                    (.tree ![0,1,5,7,4,6])
                    (.split 4
                      (.split 8
                        (.tree ![0,1,2,9,4,3])
                        (.split 13
                          (.split 12
                            (.split 10
                              (.tree ![0,1,2,7,3,4])
                              (.split 16
                                (.tree ![2,3,7,4,6,8])
                                (.other 0)))
                            (.tree ![0,1,7,3,6,4]))
                          (.tree ![0,1,2,3,4,8])))
                      (.split 12
                        (.tree ![0,1,3,7,4,6])
                        (.split 16
                          (.split 10
                            (.tree ![0,1,2,7,6,8])
                            (.tree ![2,7,5,6,8,4]))
                          (.other 0)))))
                  (.tree ![0,1,2,5,4,6])))
              (.split 15
                (.tree ![0,5,4,9,7,8])
                (.split 10
                  (.split 16
                    (.tree ![0,1,2,7,6,8])
                    (.other 0))
                  (.tree ![0,5,4,7,2,8]))))
            (.tree ![0,1,2,9,6,4]))
          (.split 16
            (.split 4
              (.tree ![0,1,6,9,4,3])
              (.split 13
                (.split 12
                  (.tree ![0,1,3,7,4,8])
                  (.split 9
                    (.tree ![0,1,2,6,9,4])
                    (.other 1)))
                (.tree ![0,1,3,6,4,8])))
            (.tree ![0,1,6,9,8,4])))
        (.tree ![0,1,2,8,9,4]))
      (.split 10
        (.split 9
          (.split 1
            (.split 7
              (.split 5
                (.split 15
                  (.split 6
                    (.split 14
                      (.split 16
                        (.tree ![4,5,9,7,6,8])
                        (.split 4
                          (.split 12
                            (.split 8
                              (.split 13
                                (.split 11
                                  (.tree ![0,1,9,4,3,5])
                                  (.other 67597))
                                (.tree ![0,1,7,8,3,4]))
                              (.tree ![1,2,7,3,6,4]))
                            (.other 2))
                          (.other 3)))
                      (.tree ![0,1,7,6,5,4]))
                    (.other 4))
                  (.tree ![0,1,7,5,8,4]))
                (.other 5))
              (.other 6))
            (.split 15
              (.tree ![0,2,5,4,9,7])
              (.tree ![0,2,5,4,7,8])))
          (.tree ![0,2,6,7,9,4]))
        (.tree ![0,2,7,8,9,4])))
    (.split 16
      (.tree ![0,8,7,6,9,4])
      (.split 13
        (.split 12
          (.tree ![0,8,7,9,4,3])
          (.other 2))
        (.tree ![0,8,3,6,4,9]))))
  (.split 12
    (.tree ![0,7,6,9,4,3])
    (.split 3
      (.split 16
        (.tree ![0,7,6,8,9,4])
        (.other 2))
      (.split 0
        (.split 7
          (.tree ![0,1,8,2,9,4])
          (.split 5
            (.tree ![1,2,8,9,4,5])
            (.split 9
              (.split 6
                (.split 16
                  (.split 10
                    (.split 8
                      (.split 14
                        (.split 4
                          (.tree ![1,2,7,3,6,4])
                          (.split 15
                            (.tree ![1,2,5,7,4,6])
                            (.split 11
                              (.split 1
                                (.tree ![0,1,2,3,5,9])
                                (.other 7))
                              (.split 1
                                (.split 13
                                  (.other 39112)
                                  (.other 8))
                                (.other 7)))))
                        (.tree ![1,2,5,8,4,6]))
                      (.tree ![0,7,3,6,2,4]))
                    (.tree ![0,7,2,6,9,4]))
                  (.other 2))
                (.tree ![0,1,2,6,9,4]))
              (.other 9))))
        (.split 1
          (.split 14
            (.split 15
              (.tree ![0,7,6,9,4,5])
              (.split 11
                (.tree ![0,7,3,5,6,9])
                (.split 9
                  (.split 10
                    (.tree ![0,2,7,5,6,4])
                    (.split 16
                      (.tree ![2,7,5,6,8,4])
                      (.other 0)))
                  (.other 10))))
            (.split 9
              (.split 16
                (.split 10
                  (.tree ![0,2,7,6,9,4])
                  (.tree ![2,7,6,8,9,4]))
                (.other 2))
              (.other 11)))
          (.tree ![0,2,5,8,4,9]))))))

theorem validTriSeparated1 :
    cover.Valid (familyTriSeparated 1).pattern
      (RootRouteCheck seamsTriSeparated (familyTriSeparated 1) routes [67585,39100]) 0 0 := by
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
