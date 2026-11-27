import FiniteLayout

namespace Graffiti199Depleted.WiderOmission

open CompactOmission

def layout23 : Layout 8 where
  port := ⟨![1,3,6], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  interior := by decide

def family23 (m : Fin 3) : Family 8 :=
  ![⟨![2,261,10,276,40,80,416,64,74],[(0,3),(0,4),(0,6),(0,7),(2,6),(3,5),(3,7),(4,6),(5,7)]⟩,
    ⟨![2,261,10,276,40,80,416,64,74],[(0,4),(0,6),(0,7),(1,4),(1,5),(1,7),(2,6),(4,6),(5,7)]⟩,
    ⟨![2,261,10,276,40,80,416,64,74],[(0,3),(0,4),(0,7),(1,4),(1,5),(1,7),(3,5),(3,7),(5,7)]⟩] m

def residues23 (m : Fin 3) : List ℕ :=
  ![[253],[254],[255,507,511]] m

private def cover23_0 : Cover 9 :=
  .split 1
    (.split 3
      (.split 4
        (.split 2
          (.split 7
            (.tree ![0,1,8,6,5,4])
            (.tree ![0,1,8,6,4,7]))
          (.split 7
            (.tree ![0,1,6,2,5,4])
            (.tree ![0,1,6,2,4,7])))
        (.split 2
          (.split 7
            (.tree ![0,1,8,6,5,4])
            (.tree ![0,1,8,6,4,7]))
          (.split 7
            (.tree ![0,6,2,5,8,4])
            (.tree ![0,6,2,4,7,8]))))
      (.split 4
        (.split 2
          (.split 7
            (.tree ![0,1,8,6,5,4])
            (.split 0
              (.split 5
                (.tree ![0,1,2,3,4,5])
                (.split 8
                  (.tree ![1,2,8,6,5,7])
                  (.tree ![0,1,7,2,5,4])))
              (.split 5
                (.tree ![0,3,2,4,8,5])
                (.split 8
                  (.tree ![1,2,8,6,5,7])
                  (.tree ![0,1,7,2,5,4])))))
          (.split 7
            (.tree ![0,1,6,2,5,4])
            (.split 0
              (.split 5
                (.tree ![0,1,2,3,4,5])
                (.split 8
                  (.tree ![1,2,8,6,5,7])
                  (.tree ![0,1,7,2,5,4])))
              (.split 5
                (.tree ![0,3,2,4,8,5])
                (.split 8
                  (.tree ![1,2,8,6,5,7])
                  (.tree ![0,1,7,2,5,4]))))))
        (.split 2
          (.split 7
            (.tree ![0,1,8,6,5,4])
            (.tree ![0,7,6,2,4,8]))
          (.split 7
            (.tree ![0,6,2,5,8,4])
            (.split 0
              (.split 5
                (.tree ![0,1,2,3,4,5])
                (.split 8
                  (.split 6
                    (.tree ![0,1,7,2,3,4])
                    (.tree ![0,7,3,2,4,8]))
                  (.tree ![0,1,7,2,5,4])))
              (.split 5
                (.tree ![0,3,2,4,8,5])
                (.split 8
                  (.split 6
                    (.tree ![0,3,7,2,4,8])
                    (.other 253))
                  (.tree ![0,1,7,2,5,4]))))))))
    (.tree ![0,1,4,2,8,5])

private def cover23_1 : Cover 9 :=
  .split 4
    (.split 0
      (.split 8
        (.split 3
          (.tree ![0,1,2,3,4,5])
          (.tree ![0,1,2,4,8,5]))
        (.tree ![2,3,4,8,5,7]))
      (.tree ![0,4,3,5,2,8]))
    (.split 0
      (.split 8
        (.split 3
          (.tree ![0,1,2,5,8,4])
          (.split 6
            (.tree ![2,3,8,6,5,7])
            (.split 7
              (.tree ![2,6,5,7,8,4])
              (.split 1
                (.split 5
                  (.split 2
                    (.tree ![0,1,2,3,6,7])
                    (.tree ![0,1,7,2,5,3]))
                  (.split 2
                    (.tree ![0,1,2,5,7,3])
                    (.tree ![0,7,6,2,5,3])))
                (.split 5
                  (.split 2
                    (.tree ![0,6,2,5,7,3])
                    (.tree ![0,1,7,2,5,3]))
                  (.split 2
                    (.tree ![0,1,2,5,7,3])
                    (.other 254)))))))
        (.tree ![2,3,4,8,5,7]))
      (.tree ![0,4,3,5,2,8]))

private def cover23_2 : Cover 9 :=
  .split 5
    (.split 4
      (.tree ![0,1,2,8,6,5])
      (.split 3
        (.split 1
          (.tree ![0,1,2,5,4,6])
          (.tree ![0,1,4,2,8,6]))
        (.tree ![1,2,4,8,6,7])))
    (.split 4
      (.tree ![0,1,2,8,6,5])
      (.split 3
        (.split 1
          (.tree ![0,1,2,5,4,6])
          (.tree ![0,1,4,2,8,6]))
        (.split 1
          (.tree ![0,1,2,4,8,6])
          (.split 7
            (.tree ![2,3,4,8,6,7])
            (.split 2
              (.split 0
                (.tree ![0,4,3,2,8,6])
                (.split 6
                  (.tree ![0,3,2,8,6,5])
                  (.split 8
                    (.tree ![0,1,2,5,7,8])
                    (.other 507))))
              (.split 0
                (.tree ![0,4,3,2,8,6])
                (.split 6
                  (.tree ![0,3,2,8,6,5])
                  (.split 8
                    (.other 255)
                    (.other 511)))))))))

def cover23 (m : Fin 3) : Cover 9 := ![cover23_0,cover23_1,cover23_2] m

set_option maxHeartbeats 2800000 in
set_option maxRecDepth 4096 in
theorem cover23_valid (m : Fin 3) :
    (cover23 m).Valid (family23 m).pattern (FullyKnown (family23 m) (residues23 m)) 0 0 := by
  fin_cases m <;> decide

set_option maxRecDepth 4096 in
theorem family23_consistent (m : Fin 3) : Consistent layout23 m (family23 m) := by
  fin_cases m <;> decide

#print axioms cover23_valid
#print axioms family23_consistent

end Graffiti199Depleted.WiderOmission
