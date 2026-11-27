import TrianglePlacement
import FastTreeCheck

namespace Graffiti199Depleted.WiderOmission
open CompactOmission
set_option maxRecDepth 8192
set_option maxHeartbeats 13000000

def layoutTriCompact : Layout 7 where
  port := ⟨![1,3,5], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  interior := by decide

def seamsTriCompact : Seams 7 0 := ![]

def familyTriCompact (m : Fin 3) : Family 7 :=
  ![⟨![2,133,10,180,40,216,32,42],[(0,3),(0,5),(0,6),(2,5),(3,6)]⟩,⟨![2,165,10,148,40,210,32,42],[(0,5),(0,6),(1,4),(1,6),(2,5)]⟩,⟨![2,141,10,150,40,208,32,42],[(0,3),(0,6),(1,4),(1,6),(3,6)]⟩] m

def edgeTriCompact (m : Fin 3) (tag : ℕ) := (familyTriCompact m).pattern.edge tag

def routesTriCompact (m : Fin 3) : List (ℕ × List (SegmentToken 7 0)) :=
  ![[],
   [],
   []] m

def routeTriCompact (m : Fin 3) (tag : ℕ) : List (SegmentToken 7 0) :=
  ((routesTriCompact m).lookup tag).getD []

def residuesTriCompact (m : Fin 3) : List ℕ :=
  ![[31],[20,11,27,15,31],[31]] m

def exceptionalTriCompact (m : Fin 3) (tag : ℕ) : Prop :=
  tag ∈ ![[31],[20,11,27,15,31],[31]] m

instance (m : Fin 3) (tag : ℕ) : Decidable (exceptionalTriCompact m tag) :=
  inferInstanceAs (Decidable (_ ∈ _))

end Graffiti199Depleted.WiderOmission
