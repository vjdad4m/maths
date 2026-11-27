import FragmentChecks
import TriCompact

namespace Graffiti199Depleted.WiderOmission
namespace TriangleCompactFlank2_31
set_option maxRecDepth 4096
set_option maxHeartbeats 7000000

abbrev e := edgeTriCompact 2 31
abbrev P : List ℕ := [0,14,27,75,91]

def singleCover : Cover 9 := (.split 0 (.split 2 (.split 1 (.split 6 (.split 4 (.split 3 (.other 0) (.tree ![0,3,2,4,8,5])) (.tree ![0,1,2,4,5,8])) (.split 4 (.tree ![1,2,4,6,7,8]) (.tree ![0,1,2,4,5,8]))) (.tree ![0,1,2,7,8,5])) (.split 1 (.tree ![0,1,2,7,8,5]) (.split 6 (.split 4 (.split 3 (.tree ![0,3,2,4,8,5]) (.other 14)) (.tree ![0,6,5,4,8,2])) (.tree ![0,6,5,8,7,2])))) (.split 2 (.split 1 (.tree ![0,1,8,2,7,5]) (.split 6 (.split 4 (.tree ![1,2,4,6,7,8]) (.split 3 (.tree ![0,3,8,2,7,5]) (.other 27))) (.split 4 (.split 3 (.tree ![0,3,8,2,4,5]) (.other 75)) (.split 3 (.tree ![0,3,8,2,7,5]) (.other 91))))) (.split 1 (.split 6 (.split 4 (.tree ![0,6,8,5,2,4]) (.tree ![0,8,2,4,5,7])) (.split 4 (.tree ![2,8,6,5,4,7]) (.tree ![0,8,2,4,5,7]))) (.split 6 (.split 4 (.tree ![0,6,8,5,2,4]) (.tree ![0,8,2,4,5,7])) (.split 4 (.tree ![2,8,6,5,4,7]) (.tree ![0,8,2,4,5,7]))))))

private theorem singleValidity : singleCover.Valid (singlePattern e)
    (ProfileKnown (n := 7) P) 160 0 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel

theorem classified : SingleChecks e (5 : Fin 8) P := certify_single singleValidity

private def left (_ : ℕ) : FragmentRoute 7 0 := ⟨0,0,[]⟩
private def right (_ : ℕ) : FragmentRoute 7 0 := ⟨0,0,[]⟩
private def pair (a d : ℕ) (b : Bool) : FragmentChoice 7 0 2 :=
  ([((27,75,false),.tree ![1,2,7,8,9,5]),((27,75,true),.route ⟨4,0,[.vertex 4,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 6,.vertex 0]⟩),((27,91,false),.tree ![1,2,7,8,9,5]),((27,91,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((75,75,false),.tree ![1,2,4,8,9,5]),((75,75,true),.keep),((75,91,false),.tree ![1,2,7,8,9,5]),((75,91,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((91,75,false),.tree ![1,2,7,8,9,5]),((91,75,true),.route ⟨4,0,[.vertex 4,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 6,.vertex 0]⟩),((91,91,false),.tree ![1,2,7,8,9,5]),((91,91,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩)].lookup (a,d,b)).getD .keep
private def step (a : ℕ) (b : Bool) : FragmentChoice 7 0 3 :=
  ([((0,false),.tree ![1,2,4,8,5,10]),((0,true),.tree ![1,2,4,8,5,10]),((14,false),.tree ![2,10,8,6,5,4]),((14,true),.tree ![2,10,8,6,5,4]),((27,false),.tree ![1,2,7,9,10,5]),((27,true),.route ⟨4,0,[.vertex 4,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 6,.vertex 0]⟩),((75,false),.tree ![1,2,4,9,10,5]),((75,true),.keep),((91,false),.tree ![1,2,7,9,10,5]),((91,true),.route ⟨4,0,[.vertex 4,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 6,.vertex 0]⟩)].lookup (a,b)).getD .keep

def rule : FragmentFlanks 7 0 layoutTriCompact e seamsTriCompact (5 : Fin 8) :=
  flanks_from_checks _ _ _ _ P 75 75 true classified
    (by decide +kernel) (by decide +kernel) (lc := left) (rc := right) (pc := pair) (sc := step)
    (by unfold LeftRoutes; decide +kernel)
    (by unfold RightRoutes; decide +kernel)
    (by unfold PairChecks; intro i; fin_cases i <;> decide +kernel)
    (by unfold StepChecks; intro _ _ i; fin_cases i <;> decide +kernel)

end TriangleCompactFlank2_31
end Graffiti199Depleted.WiderOmission
