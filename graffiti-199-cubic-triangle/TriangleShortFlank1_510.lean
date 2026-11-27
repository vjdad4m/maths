import FragmentChecks
import TriShort

namespace Graffiti199Depleted.WiderOmission
namespace TriangleShortFlank1_510
set_option maxRecDepth 4096
set_option maxHeartbeats 7000000

abbrev e := edgeTriShort 1 510
abbrev P : List ℕ := [0,102,114,118,195]

def singleCover : Cover 10 := (.split 2 (.split 4 (.split 0 (.split 5 (.split 1 (.split 6 (.split 7 (.other 0) (.tree ![1,2,5,7,3,9])) (.tree ![0,6,2,5,9,3])) (.tree ![0,1,2,5,9,3])) (.split 1 (.tree ![0,1,2,5,3,9]) (.tree ![0,1,2,4,8,9]))) (.split 5 (.split 1 (.tree ![0,1,9,2,5,3]) (.split 6 (.tree ![0,6,9,2,5,3]) (.split 7 (.tree ![1,2,5,7,9,3]) (.other 195)))) (.tree ![0,9,5,4,3,2]))) (.split 0 (.split 5 (.split 1 (.tree ![0,1,2,4,8,9]) (.tree ![0,1,2,5,9,3])) (.split 1 (.tree ![0,1,2,4,8,9]) (.split 6 (.tree ![0,6,2,5,3,9]) (.split 7 (.other 114) (.tree ![0,7,9,4,3,2]))))) (.tree ![0,9,4,3,2,8]))) (.split 4 (.split 0 (.split 5 (.split 1 (.tree ![0,1,2,5,3,9]) (.tree ![0,1,5,8,9,3])) (.split 1 (.tree ![0,1,2,4,8,9]) (.split 6 (.tree ![0,6,2,4,8,9]) (.split 7 (.other 102) (.tree ![0,7,9,2,3,4]))))) (.tree ![0,9,2,3,4,8])) (.split 0 (.split 5 (.split 1 (.tree ![0,1,2,5,3,9]) (.tree ![0,1,5,8,9,3])) (.split 1 (.tree ![0,1,5,8,9,3]) (.split 6 (.tree ![0,6,5,8,9,3]) (.split 7 (.other 118) (.tree ![0,7,9,2,5,3]))))) (.split 5 (.tree ![0,9,4,3,5,8]) (.tree ![0,9,2,5,3,8])))))

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

private def left (_ : ℕ) : FragmentRoute 8 1 := ⟨0,0,[]⟩
private def right (_ : ℕ) : FragmentRoute 8 1 := ⟨0,0,[]⟩
private def pair (a d : ℕ) (b : Bool) : FragmentChoice 8 1 2 :=
  ([((195,195,false),.tree ![1,2,5,9,10,3]),((195,195,true),.keep)].lookup (a,d,b)).getD .keep
private def step (a : ℕ) (b : Bool) : FragmentChoice 8 1 3 :=
  ([((0,false),.tree ![1,2,5,9,3,11]),((0,true),.tree ![1,2,5,9,3,11]),((102,false),.tree ![0,9,11,2,3,4]),((102,true),.tree ![0,9,11,2,3,4]),((114,false),.tree ![0,9,11,4,3,2]),((114,true),.tree ![0,9,11,4,3,2]),((118,false),.tree ![0,9,11,2,5,3]),((118,true),.tree ![0,9,11,2,5,3]),((195,false),.tree ![1,2,5,10,11,3]),((195,true),.keep)].lookup (a,b)).getD .keep

def rule : FragmentFlanks 8 1 layoutTriShort e seamsTriShort (3 : Fin 9) :=
  flanks_from_checks _ _ _ _ P 195 195 true classified
    (by decide +kernel) (by decide +kernel) (lc := left) (rc := right) (pc := pair) (sc := step)
    (by unfold LeftRoutes; decide +kernel)
    (by unfold RightRoutes; decide +kernel)
    (by unfold PairChecks; intro i; fin_cases i <;> decide +kernel)
    (by unfold StepChecks; intro _ _ i; fin_cases i <;> decide +kernel)

end TriangleShortFlank1_510
end Graffiti199Depleted.WiderOmission
