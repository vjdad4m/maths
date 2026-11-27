import FragmentChecks
import TriShort

namespace Graffiti199Depleted.WiderOmission
namespace TriangleShortFlank0_93
set_option maxRecDepth 4096
set_option maxHeartbeats 7000000

abbrev e := edgeTriShort 0 93
abbrev P : List ℕ := [0,24,96,201,204,205]

def singleCover : Cover 10 := (.split 7 (.split 4 (.split 3 (.split 5 (.split 2 (.split 6 (.split 0 (.other 0) (.tree ![0,3,9,2,4,8])) (.tree ![1,2,6,5,7,9])) (.tree ![1,2,3,9,4,7])) (.split 2 (.split 6 (.tree ![1,2,6,5,7,9]) (.split 0 (.other 96) (.tree ![0,3,9,2,4,8]))) (.tree ![1,2,3,9,4,7]))) (.tree ![1,8,3,4,7,9])) (.split 3 (.split 5 (.split 2 (.tree ![1,2,3,4,7,9]) (.split 6 (.tree ![1,2,6,9,5,7]) (.tree ![1,8,6,5,9,4]))) (.split 2 (.tree ![1,2,3,4,7,9]) (.tree ![1,2,3,9,7,5]))) (.split 5 (.split 2 (.split 6 (.split 0 (.other 24) (.tree ![0,1,6,9,5,4])) (.tree ![1,2,6,5,7,9])) (.split 6 (.tree ![1,2,6,9,5,7]) (.tree ![1,8,6,5,9,4]))) (.split 2 (.tree ![1,2,3,7,9,5]) (.split 6 (.split 0 (.tree ![0,1,2,9,4,5]) (.tree ![0,1,7,9,4,5])) (.split 0 (.tree ![0,1,2,9,4,5]) (.tree ![0,1,7,9,4,5]))))))) (.split 4 (.split 3 (.tree ![1,8,3,4,7,9]) (.split 5 (.split 2 (.split 6 (.tree ![1,2,6,5,7,9]) (.split 0 (.tree ![0,3,2,4,8,9]) (.other 201))) (.split 6 (.tree ![1,8,6,5,7,9]) (.split 0 (.other 204) (.other 205)))) (.tree ![1,8,3,4,9,5]))) (.split 3 (.split 5 (.split 2 (.split 6 (.tree ![1,2,6,5,7,9]) (.tree ![1,2,6,5,9,4])) (.split 6 (.tree ![1,8,6,5,7,9]) (.tree ![1,8,6,5,9,4]))) (.split 2 (.split 6 (.split 0 (.tree ![0,1,3,4,9,5]) (.tree ![0,1,9,2,4,5])) (.split 0 (.tree ![0,1,3,4,9,5]) (.tree ![0,1,9,2,4,5]))) (.tree ![1,2,9,4,5,7]))) (.split 5 (.split 2 (.split 6 (.tree ![1,2,6,5,7,9]) (.tree ![1,2,6,5,9,4])) (.split 6 (.tree ![1,8,6,5,7,9]) (.tree ![1,8,6,5,9,4]))) (.split 2 (.split 6 (.split 0 (.tree ![0,1,6,5,9,4]) (.tree ![0,1,9,2,4,5])) (.split 0 (.tree ![0,1,7,2,9,4]) (.tree ![0,1,9,2,4,5]))) (.tree ![1,2,9,4,5,7]))))))

private theorem singleValidity : singleCover.Valid (singlePattern e)
    (ProfileKnown (n := 8) P) 258 0 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel

theorem classified : SingleChecks e (1 : Fin 9) P := certify_single singleValidity

private def left (_ : ℕ) : FragmentRoute 8 1 := ⟨0,0,[]⟩
private def right (_ : ℕ) : FragmentRoute 8 1 := ⟨0,0,[]⟩
private def pair (a d : ℕ) (b : Bool) : FragmentChoice 8 1 2 :=
  ([((201,201,false),.tree ![1,2,3,4,9,10]),((201,201,true),.keep),((201,204,false),.tree ![0,1,9,2,8,10]),((201,204,true),.route ⟨0,2,[.vertex 0,.vertex 7,.vertex 3,.across 0 false,.vertex 6,.vertex 8,.vertex 1,.vertex 2]⟩),((201,205,false),.tree ![1,8,3,4,9,10]),((201,205,true),.route ⟨0,2,[.vertex 0,.vertex 7,.vertex 3,.across 0 false,.vertex 6,.vertex 8,.vertex 1,.vertex 2]⟩),((205,201,false),.tree ![1,8,3,4,9,10]),((205,201,true),.route ⟨2,7,[.vertex 2,.vertex 1,.vertex 8,.vertex 3,.across 0 false,.vertex 6,.vertex 0,.vertex 7]⟩),((205,204,false),.tree ![1,8,3,4,9,10]),((205,204,true),.route ⟨0,2,[.vertex 0,.vertex 7,.vertex 3,.across 0 false,.vertex 6,.vertex 8,.vertex 1,.vertex 2]⟩),((205,205,false),.tree ![1,8,3,4,9,10]),((205,205,true),.route ⟨0,2,[.vertex 0,.vertex 7,.vertex 3,.across 0 false,.vertex 6,.vertex 8,.vertex 1,.vertex 2]⟩)].lookup (a,d,b)).getD .keep
private def step (a : ℕ) (b : Bool) : FragmentChoice 8 1 3 :=
  ([((0,false),.tree ![1,2,3,4,9,11]),((0,true),.tree ![1,2,3,4,9,11]),((24,false),.tree ![0,1,9,2,11,4]),((24,true),.tree ![0,1,9,2,11,4]),((96,false),.tree ![1,2,3,4,9,11]),((96,true),.tree ![1,2,3,4,9,11]),((201,false),.tree ![1,2,3,4,10,11]),((201,true),.keep),((204,false),.tree ![0,1,10,2,8,11]),((204,true),.route ⟨2,7,[.vertex 2,.vertex 1,.vertex 8,.vertex 3,.across 0 false,.vertex 6,.vertex 0,.vertex 7]⟩),((205,false),.tree ![1,8,3,4,10,11]),((205,true),.route ⟨2,7,[.vertex 2,.vertex 1,.vertex 8,.vertex 3,.across 0 false,.vertex 6,.vertex 0,.vertex 7]⟩)].lookup (a,b)).getD .keep

def rule : FragmentFlanks 8 1 layoutTriShort e seamsTriShort (1 : Fin 9) :=
  flanks_from_checks _ _ _ _ P 201 201 true classified
    (by decide +kernel) (by decide +kernel) (lc := left) (rc := right) (pc := pair) (sc := step)
    (by unfold LeftRoutes; decide +kernel)
    (by unfold RightRoutes; decide +kernel)
    (by unfold PairChecks; intro i; fin_cases i <;> decide +kernel)
    (by unfold StepChecks; intro _ _ i; fin_cases i <;> decide +kernel)

end TriangleShortFlank0_93
end Graffiti199Depleted.WiderOmission
