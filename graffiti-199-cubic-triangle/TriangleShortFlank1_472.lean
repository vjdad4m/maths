import SparseTriangleCut
import TriShort

namespace Graffiti199Depleted.WiderOmission
namespace TriangleShortFlank1_472
set_option maxRecDepth 4096
set_option maxHeartbeats 7000000

abbrev e := edgeTriShort 1 472
abbrev P : List ℕ := [0,3,102,114,118,192]

def singleCover : Cover 10 := (.split 1 (.split 5 (.split 0 (.split 2 (.split 7 (.split 6 (.split 4 (.other 0) (.tree ![0,1,2,4,8,9])) (.tree ![2,3,6,5,7,9])) (.split 6 (.tree ![2,3,6,5,7,9]) (.split 4 (.other 192) (.tree ![0,1,2,4,8,9])))) (.tree ![0,1,2,5,3,9])) (.tree ![0,1,9,5,8,3])) (.split 0 (.tree ![0,1,5,8,9,3]) (.split 2 (.split 7 (.split 6 (.tree ![2,3,6,5,7,9]) (.tree ![0,9,6,2,7,3])) (.tree ![0,1,9,2,7,3])) (.tree ![0,9,2,5,3,8])))) (.split 5 (.split 0 (.tree ![0,1,5,8,9,3]) (.split 2 (.split 7 (.split 6 (.split 4 (.other 3) (.tree ![0,9,4,3,5,2])) (.tree ![2,3,6,5,7,9])) (.tree ![1,2,5,9,3,7])) (.split 7 (.split 6 (.tree ![2,3,6,9,5,7]) (.split 4 (.tree ![0,9,2,3,4,5]) (.tree ![0,9,4,3,5,8]))) (.split 6 (.tree ![0,9,2,3,6,5]) (.split 4 (.tree ![0,9,2,3,4,5]) (.tree ![0,9,4,3,5,8])))))) (.split 0 (.split 2 (.split 7 (.split 6 (.tree ![2,3,6,5,7,9]) (.split 4 (.tree ![0,1,2,4,8,9]) (.other 114))) (.tree ![0,1,2,9,3,7])) (.split 7 (.split 6 (.tree ![3,8,6,5,7,9]) (.split 4 (.other 102) (.other 118))) (.tree ![0,1,8,9,3,7]))) (.split 2 (.split 7 (.split 6 (.tree ![2,3,6,5,7,9]) (.tree ![0,9,6,2,7,3])) (.split 6 (.tree ![0,9,5,6,2,3]) (.split 4 (.tree ![0,9,5,4,3,2]) (.tree ![0,9,4,7,3,2])))) (.tree ![0,9,2,5,3,8])))))

private theorem singleValidity : singleCover.Valid (singlePattern e)
    (ProfileKnown (n := 8) P) 264 0 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel

theorem classified : SingleChecks e (3 : Fin 9) P := certify_single singleValidity

def crossing : ℕ → Fin 6 → Fin 11 := fun m =>
  ([(0,![1,2,5,9,3,10]),(102,![0,9,10,2,3,4]),(114,![0,9,10,4,3,2]),(118,![0,9,10,2,5,3]),(192,![1,2,5,9,3,10])].lookup m).getD (fun _ => 0)

def rule : TriangleCutChecks e (0 : Fin 9) (1 : Fin 9) (3 : Fin 9) :=
  cut_checks P 3 classified (by decide +kernel) (by decide +kernel)
    (c := crossing) (by decide +kernel)

end TriangleShortFlank1_472
end Graffiti199Depleted.WiderOmission
