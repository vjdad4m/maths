import FragmentChecks
import TriSeparated

namespace Graffiti199Depleted.WiderOmission
namespace TriangleSeparatedFlank1_67585
set_option maxRecDepth 4096
set_option maxHeartbeats 7000000

abbrev e := edgeTriSeparated 1 67585
abbrev P : List ℕ := [0,7,170,448]

def singleCover : Cover 11 := (.split 3 (.split 6 (.split 7 (.split 1 (.split 0 (.split 2 (.split 8 (.split 5 (.other 0) (.tree ![0,1,9,4,5,10])) (.tree ![3,4,9,7,8,10])) (.tree ![1,2,9,10,4,3])) (.tree ![0,1,10,9,4,3])) (.split 0 (.tree ![0,1,9,10,4,3]) (.split 2 (.tree ![1,2,9,10,4,3]) (.split 8 (.split 5 (.other 7) (.tree ![1,7,10,6,5,3])) (.tree ![3,4,9,7,8,10]))))) (.tree ![3,4,9,7,6,10])) (.split 7 (.tree ![3,4,9,7,6,10]) (.split 1 (.split 0 (.split 2 (.split 8 (.tree ![3,4,9,7,8,10]) (.split 5 (.other 448) (.tree ![0,1,9,4,5,10]))) (.tree ![1,2,9,10,4,3])) (.tree ![0,1,10,9,4,3])) (.tree ![1,9,10,4,6,3])))) (.split 6 (.split 7 (.split 1 (.split 0 (.tree ![0,1,9,4,3,10]) (.tree ![0,1,10,7,3,4])) (.tree ![1,7,10,6,3,4])) (.split 1 (.split 0 (.tree ![0,1,9,4,3,10]) (.tree ![0,10,3,7,4,6])) (.split 0 (.split 2 (.split 8 (.split 5 (.tree ![0,1,9,10,3,5]) (.other 170)) (.tree ![0,1,10,3,8,4])) (.tree ![0,2,10,3,7,4])) (.tree ![0,10,3,7,4,6])))) (.split 7 (.split 1 (.split 0 (.tree ![0,1,9,4,3,10]) (.tree ![0,1,10,7,3,4])) (.split 0 (.tree ![0,1,7,10,3,4]) (.tree ![0,10,3,6,4,7]))) (.split 1 (.split 0 (.tree ![0,1,9,4,3,10]) (.tree ![0,1,10,3,6,4])) (.split 0 (.tree ![0,1,10,3,6,4]) (.tree ![0,10,3,6,4,9]))))))

private theorem singleValidity : singleCover.Valid (singlePattern e)
    (ProfileKnown (n := 9) P) 528 0 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel

theorem classified : SingleChecks e (4 : Fin 10) P := certify_single singleValidity

private def left (_ : ℕ) : FragmentRoute 9 2 := ⟨0,0,[]⟩
private def right (_ : ℕ) : FragmentRoute 9 2 := ⟨0,0,[]⟩
private def pair (a d : ℕ) (b : Bool) : FragmentChoice 9 2 2 :=
  ([((7,448,false),.keep),((7,448,true),.tree ![1,9,10,4,11,3])].lookup (a,d,b)).getD .keep
private def step (a : ℕ) (b : Bool) : FragmentChoice 9 2 3 :=
  ([((0,false),.tree ![1,9,10,4,12,3]),((0,true),.tree ![1,9,10,4,12,3]),((7,false),.keep),((7,true),.tree ![1,9,12,4,11,3]),((170,false),.tree ![0,10,12,3,7,4]),((170,true),.tree ![0,10,12,3,7,4]),((448,false),.tree ![1,9,10,4,12,3]),((448,true),.tree ![1,9,10,4,12,3])].lookup (a,b)).getD .keep

def rule : FragmentFlanks 9 2 layoutTriSeparated e seamsTriSeparated (4 : Fin 10) :=
  flanks_from_checks _ _ _ _ P 7 448 false classified
    (by decide +kernel) (by decide +kernel) (lc := left) (rc := right) (pc := pair) (sc := step)
    (by unfold LeftRoutes; decide +kernel)
    (by unfold RightRoutes; decide +kernel)
    (by unfold PairChecks; intro i; fin_cases i <;> decide +kernel)
    (by unfold StepChecks; intro _ _ i; fin_cases i <;> decide +kernel)

end TriangleSeparatedFlank1_67585
end Graffiti199Depleted.WiderOmission
