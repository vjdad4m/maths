import FragmentChecks
import TriCompact

namespace Graffiti199Depleted.WiderOmission
namespace TriangleCompactFlank0_31
set_option maxRecDepth 4096
set_option maxHeartbeats 7000000

abbrev e := edgeTriCompact 0 31
abbrev P : List ℕ := [0,56,105,108,109]

def singleCover : Cover 9 := (.split 4 (.split 0 (.split 2 (.split 6 (.split 3 (.split 5 (.other 0) (.tree ![1,2,5,4,6,8])) (.tree ![1,2,3,4,6,8])) (.split 3 (.tree ![1,2,3,4,6,8]) (.tree ![0,3,2,4,7,8]))) (.split 6 (.tree ![0,1,6,2,7,8]) (.split 3 (.tree ![0,3,2,4,7,8]) (.split 5 (.tree ![0,5,2,4,7,8]) (.other 108))))) (.split 2 (.split 6 (.split 3 (.tree ![0,3,8,2,4,7]) (.tree ![1,2,3,4,6,8])) (.split 3 (.tree ![0,3,8,2,4,7]) (.split 5 (.tree ![1,2,5,4,6,8]) (.other 105)))) (.split 6 (.split 3 (.tree ![1,2,3,8,4,6]) (.tree ![1,7,3,4,6,8])) (.split 3 (.tree ![1,7,3,4,6,8]) (.split 5 (.tree ![1,7,5,4,6,8]) (.other 109)))))) (.split 0 (.split 2 (.split 6 (.split 3 (.tree ![1,2,3,4,6,8]) (.split 5 (.tree ![1,2,5,4,6,8]) (.other 56))) (.tree ![0,1,6,2,8,4])) (.tree ![0,1,2,7,8,4])) (.split 2 (.tree ![0,1,8,2,7,4]) (.split 6 (.tree ![0,1,6,8,7,4]) (.tree ![1,2,7,8,4,6])))))

private theorem singleValidity : singleCover.Valid (singlePattern e)
    (ProfileKnown (n := 7) P) 130 0 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel

theorem classified : SingleChecks e (1 : Fin 8) P := certify_single singleValidity

private def left (_ : ℕ) : FragmentRoute 7 0 := ⟨0,0,[]⟩
private def right (_ : ℕ) : FragmentRoute 7 0 := ⟨0,0,[]⟩
private def pair (a d : ℕ) (b : Bool) : FragmentChoice 7 0 2 :=
  ([((105,105,false),.tree ![1,2,3,4,8,9]),((105,105,true),.keep),((105,108,false),.tree ![0,1,8,2,7,9]),((105,108,true),.route ⟨0,2,[.vertex 0,.vertex 6,.vertex 3,.vertex 4,.vertex 5,.vertex 7,.vertex 1,.vertex 2]⟩),((105,109,false),.tree ![1,7,3,4,8,9]),((105,109,true),.route ⟨0,2,[.vertex 0,.vertex 6,.vertex 3,.vertex 4,.vertex 5,.vertex 7,.vertex 1,.vertex 2]⟩),((109,105,false),.tree ![1,7,3,4,8,9]),((109,105,true),.route ⟨2,6,[.vertex 2,.vertex 1,.vertex 7,.vertex 3,.vertex 4,.vertex 5,.vertex 0,.vertex 6]⟩),((109,108,false),.tree ![1,7,3,4,8,9]),((109,108,true),.route ⟨0,2,[.vertex 0,.vertex 6,.vertex 3,.vertex 4,.vertex 5,.vertex 7,.vertex 1,.vertex 2]⟩),((109,109,false),.tree ![1,7,3,4,8,9]),((109,109,true),.route ⟨0,2,[.vertex 0,.vertex 6,.vertex 3,.vertex 4,.vertex 5,.vertex 7,.vertex 1,.vertex 2]⟩)].lookup (a,d,b)).getD .keep
private def step (a : ℕ) (b : Bool) : FragmentChoice 7 0 3 :=
  ([((0,false),.tree ![1,2,3,4,8,10]),((0,true),.tree ![1,2,3,4,8,10]),((56,false),.tree ![0,1,8,2,10,4]),((56,true),.tree ![0,1,8,2,10,4]),((105,false),.tree ![1,2,3,4,9,10]),((105,true),.keep),((108,false),.tree ![0,1,9,2,7,10]),((108,true),.route ⟨2,6,[.vertex 2,.vertex 1,.vertex 7,.vertex 3,.vertex 4,.vertex 5,.vertex 0,.vertex 6]⟩),((109,false),.tree ![1,7,3,4,9,10]),((109,true),.route ⟨2,6,[.vertex 2,.vertex 1,.vertex 7,.vertex 3,.vertex 4,.vertex 5,.vertex 0,.vertex 6]⟩)].lookup (a,b)).getD .keep

def rule : FragmentFlanks 7 0 layoutTriCompact e seamsTriCompact (1 : Fin 8) :=
  flanks_from_checks _ _ _ _ P 105 105 true classified
    (by decide +kernel) (by decide +kernel) (lc := left) (rc := right) (pc := pair) (sc := step)
    (by unfold LeftRoutes; decide +kernel)
    (by unfold RightRoutes; decide +kernel)
    (by unfold PairChecks; intro i; fin_cases i <;> decide +kernel)
    (by unfold StepChecks; intro _ _ i; fin_cases i <;> decide +kernel)

end TriangleCompactFlank0_31
end Graffiti199Depleted.WiderOmission
