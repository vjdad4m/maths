import FragmentChecks
import TriCompact

namespace Graffiti199Depleted.WiderOmission
namespace TriangleCompactFlank1_11
set_option maxRecDepth 4096
set_option maxHeartbeats 7000000

abbrev e := edgeTriCompact 1 11
abbrev P : List ℕ := [0,54,85,87,99,117,119]

def singleCover : Cover 9 := (.split 1 (.split 4 (.split 0 (.split 2 (.split 6 (.split 5 (.other 0) (.tree ![0,5,4,8,3,2])) (.tree ![1,2,6,3,8,4])) (.tree ![0,1,2,3,8,4])) (.tree ![0,1,8,7,3,4])) (.split 0 (.split 2 (.tree ![0,1,2,3,4,8]) (.tree ![0,1,2,7,8,4])) (.split 2 (.tree ![0,1,8,2,7,4]) (.split 6 (.tree ![0,6,8,2,3,7]) (.split 5 (.other 85) (.other 117)))))) (.split 4 (.split 0 (.tree ![0,1,7,8,3,4]) (.split 2 (.split 6 (.tree ![1,2,6,8,3,4]) (.split 5 (.tree ![0,5,8,4,3,2]) (.other 99))) (.tree ![0,8,2,3,4,7]))) (.split 0 (.split 2 (.tree ![0,1,2,7,8,4]) (.split 6 (.split 5 (.tree ![0,5,7,3,2,8]) (.other 54)) (.tree ![0,6,8,2,3,7]))) (.split 2 (.tree ![0,8,4,3,2,7]) (.split 6 (.tree ![0,6,8,2,3,7]) (.split 5 (.other 87) (.other 119)))))))

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

private def left (_ : ℕ) : FragmentRoute 7 0 := ⟨0,0,[]⟩
private def right (_ : ℕ) : FragmentRoute 7 0 := ⟨0,0,[]⟩
private def pair (a d : ℕ) (b : Bool) : FragmentChoice 7 0 2 :=
  ([((85,85,false),.tree ![1,2,5,3,8,9]),((85,85,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((85,87,false),.tree ![0,5,8,9,7,3]),((85,87,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((85,99,false),.tree ![0,8,9,2,3,7]),((85,99,true),.route ⟨2,6,[.vertex 2,.vertex 1,.vertex 7,.vertex 3,.vertex 4,.vertex 5,.vertex 0,.vertex 6]⟩),((85,117,false),.tree ![0,1,8,9,7,3]),((85,117,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((85,119,false),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((85,119,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((87,85,false),.tree ![0,5,8,9,7,3]),((87,85,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((87,87,false),.tree ![0,5,8,9,7,3]),((87,87,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((87,99,false),.tree ![0,8,9,2,3,7]),((87,99,true),.route ⟨2,6,[.vertex 2,.vertex 1,.vertex 7,.vertex 3,.vertex 4,.vertex 5,.vertex 0,.vertex 6]⟩),((87,117,false),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((87,117,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((87,119,false),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((87,119,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((99,85,false),.tree ![0,8,9,2,3,7]),((99,85,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((99,87,false),.tree ![0,8,9,2,3,7]),((99,87,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((99,99,false),.tree ![1,2,8,9,3,4]),((99,99,true),.keep),((99,117,false),.tree ![0,8,9,2,3,7]),((99,117,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((99,119,false),.tree ![0,8,9,2,3,7]),((99,119,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((117,85,false),.tree ![0,1,8,9,7,3]),((117,85,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((117,87,false),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((117,87,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((117,99,false),.tree ![0,8,9,2,3,7]),((117,99,true),.route ⟨2,6,[.vertex 2,.vertex 1,.vertex 7,.vertex 3,.vertex 4,.vertex 5,.vertex 0,.vertex 6]⟩),((117,117,false),.tree ![0,1,8,9,7,3]),((117,117,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((117,119,false),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((117,119,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((119,85,false),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((119,85,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((119,87,false),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((119,87,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((119,99,false),.tree ![0,8,9,2,3,7]),((119,99,true),.route ⟨2,6,[.vertex 2,.vertex 1,.vertex 7,.vertex 3,.vertex 4,.vertex 5,.vertex 0,.vertex 6]⟩),((119,117,false),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((119,117,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((119,119,false),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩),((119,119,true),.route ⟨0,4,[.vertex 0,.vertex 6,.vertex 1,.vertex 2,.vertex 3,.vertex 7,.vertex 5,.vertex 4]⟩)].lookup (a,d,b)).getD .keep
private def step (a : ℕ) (b : Bool) : FragmentChoice 7 0 3 :=
  ([((0,false),.tree ![1,2,8,3,10,4]),((0,true),.tree ![1,2,8,3,10,4]),((54,false),.tree ![0,8,10,2,3,7]),((54,true),.tree ![0,8,10,2,3,7]),((85,false),.tree ![0,9,10,2,3,7]),((85,true),.route ⟨2,6,[.vertex 2,.vertex 1,.vertex 7,.vertex 3,.vertex 4,.vertex 5,.vertex 0,.vertex 6]⟩),((87,false),.tree ![0,9,10,2,3,7]),((87,true),.route ⟨2,6,[.vertex 2,.vertex 1,.vertex 7,.vertex 3,.vertex 4,.vertex 5,.vertex 0,.vertex 6]⟩),((99,false),.tree ![1,2,9,10,3,4]),((99,true),.keep),((117,false),.tree ![0,9,10,2,3,7]),((117,true),.route ⟨2,6,[.vertex 2,.vertex 1,.vertex 7,.vertex 3,.vertex 4,.vertex 5,.vertex 0,.vertex 6]⟩),((119,false),.tree ![0,9,10,2,3,7]),((119,true),.route ⟨2,6,[.vertex 2,.vertex 1,.vertex 7,.vertex 3,.vertex 4,.vertex 5,.vertex 0,.vertex 6]⟩)].lookup (a,b)).getD .keep

def rule : FragmentFlanks 7 0 layoutTriCompact e seamsTriCompact (3 : Fin 8) :=
  flanks_from_checks _ _ _ _ P 99 99 true classified
    (by decide +kernel) (by decide +kernel) (lc := left) (rc := right) (pc := pair) (sc := step)
    (by unfold LeftRoutes; decide +kernel)
    (by unfold RightRoutes; decide +kernel)
    (by unfold PairChecks; intro i; fin_cases i <;> decide +kernel)
    (by unfold StepChecks; intro _ _ i; fin_cases i <;> decide +kernel)

end TriangleCompactFlank1_11
end Graffiti199Depleted.WiderOmission
