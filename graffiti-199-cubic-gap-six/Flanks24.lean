import Rows24
import FlankWitnesses

namespace Graffiti199Depleted.WiderOmission

def edge24 (m : Fin 3) (tag : ℕ) : Fin 10 → Fin 10 → Bool :=
  (family24 m).pattern.edge tag

set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

private def single24_0 : Cover 11 :=
  .split 4
    (.split 3
      (.split 0
        (.split 8
          (.split 2
            (.split 5
              (.split 7
                (.split 6
                  (.other 0)
                  (.tree ![1,2,3,6,8,10]))
                (.tree ![1,2,7,4,8,10]))
              (.tree ![1,2,3,5,8,10]))
            (.tree ![1,2,3,10,4,8]))
          (.tree ![1,9,3,4,8,10]))
        (.split 8
          (.split 2
            (.tree ![0,3,10,2,4,9])
            (.tree ![1,2,3,10,4,8]))
          (.tree ![1,9,3,4,8,10])))
      (.split 0
        (.split 8
          (.tree ![1,9,3,4,8,10])
          (.split 2
            (.tree ![0,3,2,4,9,10])
            (.split 5
              (.split 7
                (.tree ![0,7,2,4,9,10])
                (.split 6
                  (.other 396)
                  (.tree ![0,1,2,10,6,4])))
              (.tree ![0,1,2,10,5,4]))))
        (.split 8
          (.tree ![1,9,3,4,8,10])
          (.split 2
            (.split 5
              (.split 7
                (.tree ![1,2,7,4,8,10])
                (.split 6
                  (.other 393)
                  (.tree ![0,1,10,2,6,4])))
              (.tree ![0,1,10,2,5,4]))
            (.split 5
              (.split 7
                (.tree ![1,9,7,4,8,10])
                (.split 6
                  (.other 397)
                  (.tree ![1,2,10,6,8,4])))
              (.tree ![1,2,10,5,8,4]))))))
    (.split 3
      (.split 0
        (.split 8
          (.split 2
            (.tree ![1,2,3,4,8,10])
            (.tree ![0,1,8,2,10,4]))
          (.split 2
            (.tree ![0,1,8,2,10,4])
            (.tree ![0,1,2,9,10,4])))
        (.split 8
          (.tree ![0,1,8,10,9,4])
          (.split 2
            (.tree ![0,1,10,2,9,4])
            (.tree ![1,2,9,10,4,8]))))
      (.split 0
        (.split 8
          (.split 2
            (.split 5
              (.tree ![1,2,3,5,8,10])
              (.split 7
                (.tree ![1,2,7,4,8,10])
                (.split 6
                  (.tree ![1,2,3,6,8,10])
                  (.other 248))))
            (.tree ![0,1,8,2,10,4]))
          (.split 2
            (.tree ![0,1,8,2,10,4])
            (.tree ![0,1,2,9,10,4])))
        (.split 8
          (.tree ![0,1,8,10,9,4])
          (.split 2
            (.tree ![0,1,10,2,9,4])
            (.tree ![1,2,9,10,4,8])))))

private def pair24_0 : ℕ → ℕ → Bool → FlankWitness 9 2
  | 393,393,false => .tree ![1,2,3,4,10,11]
  | 393,396,false => .tree ![0,1,10,2,9,11]
  | 393,396,true => .route [0,8,3,4,5,6,7,9,1,2] false
  | 393,397,false => .tree ![1,9,3,4,10,11]
  | 393,397,true => .route [0,8,3,4,5,6,7,9,1,2] false
  | 397,393,false => .tree ![1,9,3,4,10,11]
  | 397,393,true => .route [2,1,9,3,4,5,6,7,0,8] false
  | 397,396,false => .tree ![1,9,3,4,10,11]
  | 397,396,true => .route [0,8,3,4,5,6,7,9,1,2] false
  | 397,397,false => .tree ![1,9,3,4,10,11]
  | 397,397,true => .route [0,8,3,4,5,6,7,9,1,2] false
  | _,_,_ => .pass

private def step24_0 : ℕ → Bool → FlankWitness 9 3
  | 0,false => .tree ![1,2,3,4,10,12]
  | 0,true => .tree ![1,2,3,4,10,12]
  | 248,false => .tree ![0,1,10,2,12,4]
  | 248,true => .tree ![0,1,10,2,12,4]
  | 393,false => .tree ![1,2,3,4,11,12]
  | 396,false => .tree ![0,1,11,2,9,12]
  | 396,true => .route [2,1,9,3,4,5,6,7,0,8] false
  | 397,false => .tree ![1,9,3,4,11,12]
  | 397,true => .route [2,1,9,3,4,5,6,7,0,8] false
  | _,_ => .pass

def flanks24_0 : FlankRules 9 (edge24 0 8153) (layout24.port 0) where
  profiles := [0,248,393,396,397]
  boundary := 393
  outerChord := by decide
  boundaryRight := by decide
  single := certify_single (n := 9) (e := edge24 0 8153) (mate := layout24.port 0)
    (C := single24_0) (by decide)
  pair := certify_pair (cert := pair24_0) (by decide)
  step := certify_step (cert := step24_0) (by decide)

#print axioms flanks24_0

private def single24_1 : Cover 11 :=
  .split 0
    (.split 1
      (.split 2
        (.split 4
          (.split 5
            (.split 6
              (.split 7
                (.split 8
                  (.other 0)
                  (.tree ![1,2,5,8,3,10]))
                (.tree ![0,7,2,5,10,3]))
              (.tree ![0,1,2,6,3,10]))
            (.tree ![0,1,2,5,3,10]))
          (.tree ![0,1,2,4,9,10]))
        (.split 4
          (.tree ![0,1,2,4,9,10])
          (.split 5
            (.tree ![0,1,2,5,3,10])
            (.tree ![0,1,5,9,10,3]))))
      (.split 2
        (.split 4
          (.tree ![0,1,2,4,9,10])
          (.split 5
            (.tree ![0,1,2,5,10,3])
            (.split 6
              (.tree ![0,1,2,6,10,3])
              (.split 7
                (.tree ![0,7,2,5,3,10])
                (.split 8
                  (.other 242)
                  (.tree ![0,8,10,4,3,2]))))))
        (.split 4
          (.split 5
            (.tree ![0,1,5,9,10,3])
            (.split 6
              (.tree ![0,1,6,9,10,3])
              (.split 7
                (.tree ![0,7,2,4,9,10])
                (.split 8
                  (.other 230)
                  (.tree ![0,8,10,2,3,4])))))
          (.split 5
            (.tree ![0,1,5,9,10,3])
            (.split 6
              (.tree ![0,1,6,9,10,3])
              (.split 7
                (.tree ![0,7,5,9,10,3])
                (.split 8
                  (.other 246)
                  (.tree ![0,8,10,2,5,3]))))))))
    (.split 1
      (.split 2
        (.split 4
          (.split 5
            (.tree ![0,1,10,2,5,3])
            (.tree ![0,10,5,4,3,2]))
          (.tree ![0,10,4,3,2,9]))
        (.split 4
          (.tree ![0,10,2,3,4,9])
          (.split 5
            (.tree ![0,1,10,5,9,3])
            (.tree ![0,10,2,5,3,9]))))
      (.split 2
        (.split 4
          (.split 5
            (.split 6
              (.split 7
                (.tree ![0,7,10,2,5,3])
                (.split 8
                  (.tree ![1,2,5,8,10,3])
                  (.other 387)))
              (.tree ![0,10,6,4,3,2]))
            (.tree ![0,10,5,4,3,2]))
          (.tree ![0,10,4,3,2,9]))
        (.split 4
          (.tree ![0,10,2,3,4,9])
          (.split 5
            (.tree ![0,10,4,3,5,9])
            (.tree ![0,10,2,5,3,9])))))

private def pair24_1 : ℕ → ℕ → Bool → FlankWitness 9 2
  | 387,387,false => .tree ![1,2,5,10,11,3]
  | _,_,_ => .pass

private def step24_1 : ℕ → Bool → FlankWitness 9 3
  | 0,false => .tree ![1,2,5,10,3,12]
  | 0,true => .tree ![1,2,5,10,3,12]
  | 230,false => .tree ![0,10,12,2,3,4]
  | 230,true => .tree ![0,10,12,2,3,4]
  | 242,false => .tree ![0,10,12,4,3,2]
  | 242,true => .tree ![0,10,12,4,3,2]
  | 246,false => .tree ![0,10,12,2,5,3]
  | 246,true => .tree ![0,10,12,2,5,3]
  | 387,false => .tree ![1,2,5,11,12,3]
  | _,_ => .pass

def flanks24_1 : FlankRules 9 (edge24 1 7932) (layout24.port 1) where
  profiles := [0,230,242,246,387]
  boundary := 387
  outerChord := by decide
  boundaryRight := by decide
  single := certify_single (n := 9) (e := edge24 1 7932) (mate := layout24.port 1)
    (C := single24_1) (by decide)
  pair := certify_pair (cert := pair24_1) (by decide)
  step := certify_step (cert := step24_1) (by decide)

#print axioms flanks24_1

end Graffiti199Depleted.WiderOmission
