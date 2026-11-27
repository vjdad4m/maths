import TrianglePlacement
import FastTreeCheck

namespace Graffiti199Depleted.WiderOmission
open CompactOmission
set_option maxRecDepth 8192
set_option maxHeartbeats 13000000

def layoutTriShort : Layout 8 where
  port := ⟨![1,3,6], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  interior := by decide

def seamsTriShort : Seams 8 1 := ![(4,5)]

def familyTriShort (m : Fin 3) : Family 8 :=
  ![⟨![2,261,10,340,8,64,424,64,74],[(0,3),(0,4),(0,6),(0,7),(2,6),(3,5),(3,7),(4,5),(4,6),(5,7)]⟩,⟨![2,325,10,276,8,64,418,64,74],[(0,4),(0,6),(0,7),(1,4),(1,5),(1,7),(2,6),(4,5),(4,6),(5,7)]⟩,⟨![2,269,10,278,8,64,416,64,74],[(0,3),(0,4),(0,7),(1,4),(1,5),(1,7),(3,5),(3,7),(4,5),(5,7)]⟩] m

def edgeTriShort (m : Fin 3) (tag : ℕ) := (familyTriShort m).pattern.edge tag

def routesTriShort (m : Fin 3) : List (ℕ × List (SegmentToken 8 1)) :=
  ![[(528,[.vertex 0,.vertex 1,.vertex 2,.vertex 6,.vertex 8,.vertex 3,.across 0 false,.vertex 7]),
    (533,[.vertex 0,.vertex 1,.vertex 2,.vertex 6,.vertex 8,.vertex 3,.across 0 false,.vertex 7]),
    (790,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 8,.vertex 6,.across 0 false,.vertex 7]),
    (791,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 8,.vertex 6,.across 0 false,.vertex 7]),
    (887,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 8,.vertex 6,.across 0 false,.vertex 7])],
   [(576,[.vertex 0,.vertex 1,.vertex 2,.vertex 6,.vertex 8,.vertex 3,.across 0 false,.vertex 7]),
    (840,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 8,.vertex 6,.across 0 false,.vertex 7]),
    (835,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 8,.vertex 6,.across 0 false,.vertex 7]),
    (843,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 8,.vertex 6,.across 0 false,.vertex 7]),
    (891,[.vertex 0,.vertex 1,.vertex 2,.vertex 3,.vertex 8,.vertex 6,.across 0 false,.vertex 7])],
   [(511,[.vertex 0,.across 0 false,.vertex 1,.vertex 2,.vertex 3,.vertex 8,.vertex 6,.vertex 7]),
    (763,[.vertex 0,.across 0 false,.vertex 1,.vertex 2,.vertex 3,.vertex 8,.vertex 6,.vertex 7]),
    (1019,[.vertex 0,.across 0 false,.vertex 1,.vertex 2,.vertex 3,.vertex 8,.vertex 6,.vertex 7]),
    (767,[.vertex 0,.across 0 false,.vertex 1,.vertex 2,.vertex 3,.vertex 8,.vertex 6,.vertex 7]),
    (1023,[.vertex 0,.across 0 false,.vertex 1,.vertex 2,.vertex 3,.vertex 8,.vertex 6,.vertex 7])]] m

def routeTriShort (m : Fin 3) (tag : ℕ) : List (SegmentToken 8 1) :=
  ((routesTriShort m).lookup tag).getD []

def residuesTriShort (m : Fin 3) : List ℕ :=
  ![[528,533,790,791,887,93,509],[576,840,835,843,891,472,510],[752,511,763,1019,767,1023]] m

def exceptionalTriShort (m : Fin 3) (tag : ℕ) : Prop :=
  tag ∈ ![[93,509],[472,510],[752]] m

instance (m : Fin 3) (tag : ℕ) : Decidable (exceptionalTriShort m tag) :=
  inferInstanceAs (Decidable (_ ∈ _))

end Graffiti199Depleted.WiderOmission
