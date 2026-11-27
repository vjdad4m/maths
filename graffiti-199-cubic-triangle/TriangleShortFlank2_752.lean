import FragmentChecks
import TriShort

namespace Graffiti199Depleted.WiderOmission
namespace TriangleShortFlank2_752
set_option maxRecDepth 4096
set_option maxHeartbeats 7000000

abbrev e := edgeTriShort 2 752
abbrev P : List ℕ := [0,3,14,24,31,46,142,174]

def singleCover : Cover 10 := (.split 0 (.split 1 (.split 2 (.split 3 (.split 4 (.split 5 (.split 7 (.other 0) (.tree ![0,1,2,7,6,9])) (.tree ![0,1,2,5,6,9])) (.split 5 (.tree ![2,3,4,5,9,6]) (.tree ![0,1,2,5,6,9]))) (.split 4 (.split 5 (.tree ![2,3,4,5,9,6]) (.tree ![0,1,2,5,6,9])) (.split 5 (.split 7 (.other 24) (.tree ![0,1,2,7,6,9])) (.tree ![0,1,2,5,6,9])))) (.tree ![0,1,2,8,9,6])) (.split 2 (.tree ![0,1,2,8,9,6]) (.split 3 (.split 4 (.tree ![2,3,9,4,8,6]) (.tree ![0,1,8,9,6,4])) (.split 4 (.split 5 (.split 7 (.other 14) (.other 142)) (.split 7 (.other 46) (.other 174))) (.tree ![0,1,8,9,6,4]))))) (.split 1 (.split 2 (.split 3 (.split 4 (.split 5 (.tree ![0,1,9,2,5,6]) (.tree ![0,9,5,3,2,4])) (.split 5 (.tree ![0,1,9,2,5,6]) (.tree ![0,9,5,3,6,2]))) (.tree ![0,9,3,2,8,6])) (.split 3 (.split 4 (.tree ![2,3,9,4,8,6]) (.split 5 (.tree ![0,9,2,3,5,6]) (.tree ![0,9,2,4,5,6]))) (.split 4 (.tree ![0,9,3,4,8,6]) (.split 5 (.tree ![0,1,9,5,4,6]) (.tree ![0,9,2,4,5,6]))))) (.split 2 (.split 3 (.split 4 (.split 5 (.split 7 (.other 3) (.tree ![0,9,7,3,2,4])) (.tree ![0,9,5,3,2,4])) (.split 5 (.tree ![2,3,4,5,9,6]) (.tree ![0,9,5,3,6,2]))) (.tree ![0,9,3,2,8,6])) (.split 3 (.split 4 (.tree ![2,3,9,4,8,6]) (.split 5 (.tree ![0,9,2,3,5,6]) (.tree ![0,9,2,4,5,6]))) (.split 4 (.tree ![0,9,3,4,8,6]) (.split 5 (.split 7 (.other 31) (.tree ![0,9,2,4,7,5])) (.tree ![0,9,2,4,5,6])))))))

private theorem singleValidity : singleCover.Valid (singlePattern e)
    (ProfileKnown (n := 8) P) 320 0 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel

theorem classified : SingleChecks e (6 : Fin 9) P := certify_single singleValidity

private def left (m : ℕ) : FragmentRoute 8 1 := ([(142,⟨0,2,[.vertex 0,.vertex 1,.vertex 8,.vertex 6,.vertex 7,.across 0 true,.vertex 3,.vertex 2]⟩),(174,⟨0,2,[.vertex 0,.vertex 1,.vertex 8,.vertex 6,.vertex 7,.across 0 true,.vertex 3,.vertex 2]⟩)].lookup m).getD ⟨0,0,[]⟩
private def right (_ : ℕ) : FragmentRoute 8 1 := ⟨0,0,[]⟩
private def pair (a d : ℕ) (b : Bool) : FragmentChoice 8 1 2 :=
  ([((3,142,false),.route ⟨0,2,[.vertex 0,.vertex 1,.vertex 8,.vertex 6,.vertex 7,.across 0 true,.vertex 3,.vertex 2]⟩),((3,142,true),.tree ![0,9,10,3,4,5]),((3,174,false),.route ⟨0,2,[.vertex 0,.vertex 1,.vertex 8,.vertex 6,.vertex 7,.across 0 true,.vertex 3,.vertex 2]⟩),((3,174,true),.tree ![0,9,10,2,5,6]),((31,142,false),.tree ![0,9,3,5,10,6]),((31,142,true),.tree ![0,9,4,10,7,5]),((31,174,false),.tree ![0,9,2,4,10,5]),((31,174,true),.tree ![0,9,4,10,5,6])].lookup (a,d,b)).getD .keep
private def step (_ : ℕ) (_ : Bool) : FragmentChoice 8 1 3 :=
  .keep

def rule : FragmentFlanks 8 1 layoutTriShort e seamsTriShort (6 : Fin 9) :=
  flanks_from_checks _ _ _ _ P 260 0 false classified
    (by decide +kernel) (by decide +kernel) (lc := left) (rc := right) (pc := pair) (sc := step)
    (by unfold LeftRoutes; decide +kernel)
    (by unfold RightRoutes; decide +kernel)
    (by unfold PairChecks; intro i; fin_cases i <;> decide +kernel)
    (by unfold StepChecks; intro h; exfalso; exact (by decide +kernel : 260 ∉ P) h)

end TriangleShortFlank2_752
end Graffiti199Depleted.WiderOmission
