import SparseTriangleCut
import TriCompact

namespace Graffiti199Depleted.WiderOmission
namespace TriangleCompactFlank1_20
set_option maxRecDepth 4096
set_option maxHeartbeats 7000000

abbrev e := edgeTriCompact 1 20
abbrev P : List ℕ := [0,3,20,22,38,50,52,54,96]

def singleCover : Cover 9 := (.split 6 (.split 0 (.split 1 (.split 2 (.split 5 (.split 4 (.other 0) (.tree ![0,1,2,4,7,8])) (.split 4 (.tree ![2,5,4,6,7,8]) (.tree ![0,1,2,4,7,8]))) (.split 5 (.split 4 (.tree ![0,1,2,4,7,8]) (.other 20)) (.split 4 (.tree ![0,1,2,4,7,8]) (.other 52)))) (.split 2 (.split 5 (.split 4 (.tree ![0,1,2,4,7,8]) (.tree ![2,5,4,6,7,8])) (.split 4 (.tree ![0,1,2,4,7,8]) (.other 50))) (.split 5 (.split 4 (.tree ![2,5,8,4,6,7]) (.other 22)) (.split 4 (.other 38) (.other 54))))) (.split 1 (.split 2 (.split 5 (.split 4 (.tree ![0,1,8,2,4,7]) (.tree ![0,8,4,5,2,6])) (.tree ![0,8,5,2,6,3])) (.split 5 (.tree ![0,8,2,3,5,6]) (.tree ![0,8,5,6,7,3]))) (.split 2 (.split 5 (.split 4 (.other 3) (.tree ![0,8,4,5,2,6])) (.tree ![0,8,5,2,6,3])) (.split 5 (.tree ![0,8,2,3,5,6]) (.tree ![0,8,5,6,7,3]))))) (.split 0 (.split 1 (.split 2 (.split 5 (.split 4 (.tree ![2,5,4,6,7,8]) (.tree ![0,1,2,4,7,8])) (.split 4 (.other 96) (.tree ![0,1,2,4,7,8]))) (.tree ![0,1,2,3,8,6])) (.tree ![0,1,7,8,3,6])) (.split 1 (.tree ![0,1,8,7,6,3]) (.split 2 (.split 5 (.tree ![0,8,6,5,2,3]) (.split 4 (.tree ![0,8,5,2,4,7]) (.tree ![0,8,4,6,3,2]))) (.tree ![0,8,2,6,3,7])))))

private theorem singleValidity : singleCover.Valid (singlePattern e)
    (ProfileKnown (n := 7) P) 136 0 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel

theorem classified : SingleChecks e (3 : Fin 8) P := certify_single singleValidity

def crossing : ℕ → Fin 6 → Fin 10 := fun m =>
  ([(0,![1,2,4,7,8,9]),(20,![0,8,9,2,3,5]),(22,![0,8,9,2,3,5]),(38,![0,8,9,2,3,4]),(50,![0,8,9,4,3,2]),(52,![0,8,9,2,3,7]),(54,![0,8,9,2,3,7]),(96,![0,8,9,5,2,3])].lookup m).getD (fun _ => 0)

def rule : TriangleCutChecks e (0 : Fin 8) (1 : Fin 8) (3 : Fin 8) :=
  cut_checks P 3 classified (by decide +kernel) (by decide +kernel)
    (c := crossing) (by decide +kernel)

end TriangleCompactFlank1_20
end Graffiti199Depleted.WiderOmission
