import TrianglePlacement
import RootRoutes

namespace Graffiti199Depleted.WiderOmission
open CompactOmission
set_option maxRecDepth 8192
set_option maxHeartbeats 13000000

def layoutTriSeparated : Layout 9 where
  port := ⟨![1,4,7], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  interior := by decide

def seamsTriSeparated : Seams 9 2 := ![(2,3),(5,6)]

def familyTriSeparated (m : Fin 3) : Family 9 :=
  ![⟨![2,517,2,16,680,16,128,848,128,146],[(0,2),(0,4),(0,5),(0,7),(0,8),(2,3),(2,4),(2,6),(2,7),(3,5),(3,7),(3,8),(4,6),(4,8),(5,6),(5,7),(6,8)]⟩,⟨![2,645,2,16,552,16,128,834,128,146],[(0,2),(0,5),(0,7),(0,8),(1,3),(1,5),(1,6),(1,8),(2,3),(2,6),(2,7),(3,5),(3,7),(3,8),(5,6),(5,7),(6,8)]⟩,⟨![2,533,2,16,554,16,128,832,128,146],[(0,2),(0,4),(0,5),(0,8),(1,3),(1,5),(1,6),(1,8),(2,3),(2,4),(2,6),(3,5),(3,8),(4,6),(4,8),(5,6),(6,8)]⟩] m

def edgeTriSeparated (m : Fin 3) (tag : ℕ) := (familyTriSeparated m).pattern.edge tag

def exceptionalTriSeparated (m : Fin 3) (tag : ℕ) : Prop :=
  tag ∈ ![[53579,66049],[67585,39100],[91088,67585]] m

instance (m : Fin 3) (tag : ℕ) : Decidable (exceptionalTriSeparated m tag) :=
  inferInstanceAs (Decidable (_ ∈ _))

end Graffiti199Depleted.WiderOmission
