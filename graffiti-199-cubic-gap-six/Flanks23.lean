import Rows23
import FlankWitnesses

namespace Graffiti199Depleted.WiderOmission

def edge23 (m : Fin 3) (tag : ℕ) : Fin 9 → Fin 9 → Bool :=
  (family23 m).pattern.edge tag

set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

private def single23_0 : Cover 10 :=
  .split 4
    (.split 7
      (.split 0
        (.split 3
          (.split 2
            (.split 5
              (.split 6
                (.other 0)
                (.tree ![1,2,6,4,7,9]))
              (.tree ![1,2,3,5,7,9]))
            (.tree ![1,2,3,9,4,7]))
          (.tree ![1,8,3,4,7,9]))
        (.split 3
          (.split 2
            (.tree ![0,3,9,2,4,8])
            (.tree ![1,2,3,9,4,7]))
          (.tree ![1,8,3,4,7,9])))
      (.split 0
        (.split 3
          (.tree ![1,8,3,4,7,9])
          (.split 2
            (.tree ![0,3,2,4,8,9])
            (.split 5
              (.split 6
                (.tree ![0,6,2,4,8,9])
                (.other 204))
              (.tree ![0,1,2,9,5,4]))))
        (.split 3
          (.tree ![1,8,3,4,7,9])
          (.split 2
            (.split 5
              (.split 6
                (.tree ![1,2,6,4,7,9])
                (.other 201))
              (.tree ![0,1,9,2,5,4]))
            (.split 5
              (.split 6
                (.tree ![1,8,6,4,7,9])
                (.other 205))
              (.tree ![1,2,9,5,7,4]))))))
    (.split 7
      (.split 0
        (.split 3
          (.split 2
            (.tree ![1,2,3,4,7,9])
            (.tree ![0,1,7,2,9,4]))
          (.split 2
            (.split 5
              (.tree ![1,2,3,5,7,9])
              (.split 6
                (.tree ![1,2,6,4,7,9])
                (.other 120)))
            (.tree ![0,1,7,2,9,4])))
        (.tree ![0,1,7,9,8,4]))
      (.split 0
        (.split 3
          (.split 2
            (.tree ![0,1,7,2,9,4])
            (.tree ![0,1,2,8,9,4]))
          (.split 2
            (.tree ![0,1,7,2,9,4])
            (.tree ![0,1,2,8,9,4])))
        (.split 3
          (.split 2
            (.tree ![0,1,9,2,8,4])
            (.tree ![1,2,8,9,4,7]))
          (.split 2
            (.tree ![0,1,9,2,8,4])
            (.tree ![1,2,8,9,4,7])))))

private def pair23_0 : ℕ → ℕ → Bool → FlankWitness 8 2
  | 201,201,false => .tree ![1,2,3,4,9,10]
  | 201,204,false => .tree ![0,1,9,2,8,10]
  | 201,204,true => .route [0,7,3,4,5,6,8,1,2] false
  | 201,205,false => .tree ![1,8,3,4,9,10]
  | 201,205,true => .route [0,7,3,4,5,6,8,1,2] false
  | 205,201,false => .tree ![1,8,3,4,9,10]
  | 205,201,true => .route [2,1,8,3,4,5,6,0,7] false
  | 205,204,false => .tree ![1,8,3,4,9,10]
  | 205,204,true => .route [0,7,3,4,5,6,8,1,2] false
  | 205,205,false => .tree ![1,8,3,4,9,10]
  | 205,205,true => .route [0,7,3,4,5,6,8,1,2] false
  | _,_,_ => .pass

private def step23_0 : ℕ → Bool → FlankWitness 8 3
  | 0,false => .tree ![1,2,3,4,9,11]
  | 0,true => .tree ![1,2,3,4,9,11]
  | 120,false => .tree ![0,1,9,2,11,4]
  | 120,true => .tree ![0,1,9,2,11,4]
  | 201,false => .tree ![1,2,3,4,10,11]
  | 204,false => .tree ![0,1,10,2,8,11]
  | 204,true => .route [2,1,8,3,4,5,6,0,7] false
  | 205,false => .tree ![1,8,3,4,10,11]
  | 205,true => .route [2,1,8,3,4,5,6,0,7] false
  | _,_ => .pass

def flanks23_0 : FlankRules 8 (edge23 0 253) (layout23.port 0) where
  profiles := [0,120,201,204,205]
  boundary := 201
  outerChord := by decide
  boundaryRight := by decide
  single := certify_single (n := 8) (e := edge23 0 253) (mate := layout23.port 0)
    (C := single23_0) (by decide)
  pair := certify_pair (cert := pair23_0) (by decide)
  step := certify_step (cert := step23_0) (by decide)

#print axioms flanks23_0

private def single23_1 : Cover 10 :=
  .split 0
    (.split 1
      (.split 5
        (.split 4
          (.split 2
            (.split 7
              (.split 6
                (.other 0)
                (.tree ![0,6,2,5,9,3]))
              (.tree ![1,2,5,7,3,9]))
            (.tree ![0,1,2,5,3,9]))
          (.split 2
            (.tree ![0,1,2,4,8,9])
            (.tree ![0,1,2,5,3,9])))
        (.tree ![0,1,5,8,9,3]))
      (.split 5
        (.tree ![0,1,5,8,9,3])
        (.split 4
          (.split 2
            (.tree ![0,1,2,4,8,9])
            (.split 7
              (.split 6
                (.tree ![0,6,2,4,8,9])
                (.other 102))
              (.tree ![0,7,9,2,3,4])))
          (.split 2
            (.split 7
              (.split 6
                (.tree ![0,6,2,5,3,9])
                (.other 114))
              (.tree ![0,7,9,4,3,2]))
            (.split 7
              (.split 6
                (.tree ![0,6,5,8,9,3])
                (.other 118))
              (.tree ![0,7,9,2,5,3]))))))
    (.split 1
      (.split 5
        (.tree ![0,1,9,5,8,3])
        (.split 4
          (.split 2
            (.tree ![0,9,5,4,3,2])
            (.tree ![0,9,2,3,4,8]))
          (.split 2
            (.tree ![0,9,4,3,2,8])
            (.tree ![0,9,2,5,3,8]))))
      (.split 5
        (.split 4
          (.split 2
            (.split 7
              (.tree ![1,2,5,7,9,3])
              (.split 6
                (.tree ![0,6,9,2,5,3])
                (.other 195)))
            (.tree ![0,9,2,3,4,5]))
          (.tree ![0,9,4,3,5,8]))
        (.split 4
          (.split 2
            (.tree ![0,9,5,4,3,2])
            (.tree ![0,9,2,3,4,8]))
          (.split 2
            (.tree ![0,9,4,3,2,8])
            (.tree ![0,9,2,5,3,8])))))

private def pair23_1 : ℕ → ℕ → Bool → FlankWitness 8 2
  | 195,195,false => .tree ![1,2,5,9,10,3]
  | _,_,_ => .pass

private def step23_1 : ℕ → Bool → FlankWitness 8 3
  | 0,false => .tree ![1,2,5,9,3,11]
  | 0,true => .tree ![1,2,5,9,3,11]
  | 102,false => .tree ![0,9,11,2,3,4]
  | 102,true => .tree ![0,9,11,2,3,4]
  | 114,false => .tree ![0,9,11,4,3,2]
  | 114,true => .tree ![0,9,11,4,3,2]
  | 118,false => .tree ![0,9,11,2,5,3]
  | 118,true => .tree ![0,9,11,2,5,3]
  | 195,false => .tree ![1,2,5,10,11,3]
  | _,_ => .pass

def flanks23_1 : FlankRules 8 (edge23 1 254) (layout23.port 1) where
  profiles := [0,102,114,118,195]
  boundary := 195
  outerChord := by decide
  boundaryRight := by decide
  single := certify_single (n := 8) (e := edge23 1 254) (mate := layout23.port 1)
    (C := single23_1) (by decide)
  pair := certify_pair (cert := pair23_1) (by decide)
  step := certify_step (cert := step23_1) (by decide)

#print axioms flanks23_1

end Graffiti199Depleted.WiderOmission
