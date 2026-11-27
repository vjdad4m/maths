import FragmentChecks
import TriSeparated

namespace Graffiti199Depleted.WiderOmission
namespace TriangleSeparatedFlank0_66049
set_option maxRecDepth 4096
set_option maxHeartbeats 7000000

abbrev e := edgeTriSeparated 0 66049
abbrev P : List ℕ := [0,56,149,448]

def singleCover : Cover 11 := (.split 6 (.split 0 (.split 3 (.split 7 (.split 4 (.split 2 (.split 8 (.split 5 (.other 0) (.tree ![0,1,9,4,5,10])) (.tree ![0,1,9,7,8,10])) (.tree ![1,2,9,10,4,3])) (.tree ![0,1,9,4,3,10])) (.tree ![0,1,9,7,6,10])) (.split 7 (.split 4 (.tree ![0,1,9,4,3,10]) (.split 2 (.split 8 (.split 5 (.tree ![0,1,9,4,5,10]) (.other 56)) (.tree ![0,1,9,7,8,10])) (.tree ![0,2,10,4,7,6]))) (.tree ![0,1,9,7,6,10]))) (.split 3 (.split 7 (.split 4 (.tree ![0,1,10,9,4,3]) (.tree ![0,1,10,4,3,7])) (.split 4 (.tree ![0,1,10,9,4,3]) (.split 2 (.tree ![0,2,10,4,3,9]) (.split 8 (.split 5 (.other 149) (.tree ![0,1,10,5,7,3])) (.tree ![0,1,10,4,8,3]))))) (.split 7 (.split 4 (.tree ![0,1,10,3,4,7]) (.tree ![0,1,10,4,7,6])) (.tree ![0,1,10,3,7,6])))) (.split 0 (.split 3 (.split 7 (.tree ![0,1,9,7,6,10]) (.split 4 (.split 2 (.split 8 (.tree ![0,1,9,7,8,10]) (.split 5 (.other 448) (.tree ![0,1,9,4,5,10]))) (.tree ![1,2,9,10,4,3])) (.tree ![0,1,9,4,3,10]))) (.split 7 (.tree ![0,1,9,7,6,10]) (.tree ![0,1,9,7,10,3]))) (.split 3 (.split 7 (.split 4 (.tree ![0,1,10,9,4,3]) (.tree ![0,1,10,4,3,7])) (.split 4 (.tree ![0,1,10,9,4,3]) (.tree ![0,1,10,4,6,3]))) (.tree ![0,1,10,9,3,6]))))

private theorem singleValidity : singleCover.Valid (singlePattern e)
    (ProfileKnown (n := 9) P) 514 0 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel

theorem classified : SingleChecks e (1 : Fin 10) P := certify_single singleValidity

private def left (_ : ℕ) : FragmentRoute 9 2 := ⟨0,0,[]⟩
private def right (_ : ℕ) : FragmentRoute 9 2 := ⟨0,0,[]⟩
private def pair (a d : ℕ) (b : Bool) : FragmentChoice 9 2 2 :=
  ([((149,448,false),.route ⟨4,8,[.vertex 4,.vertex 7,.vertex 9,.vertex 1,.vertex 0,.across 0 false,.across 1 false,.vertex 8]⟩),((149,448,true),.tree ![0,1,10,4,11,3])].lookup (a,d,b)).getD .keep
private def step (_ : ℕ) (_ : Bool) : FragmentChoice 9 2 3 :=
  .keep

def rule : FragmentFlanks 9 2 layoutTriSeparated e seamsTriSeparated (1 : Fin 10) :=
  flanks_from_checks _ _ _ _ P 516 0 false classified
    (by decide +kernel) (by decide +kernel) (lc := left) (rc := right) (pc := pair) (sc := step)
    (by unfold LeftRoutes; decide +kernel)
    (by unfold RightRoutes; decide +kernel)
    (by unfold PairChecks; intro i; fin_cases i <;> decide +kernel)
    (by unfold StepChecks; intro h; exfalso; exact (by decide +kernel : 516 ∉ P) h)

end TriangleSeparatedFlank0_66049
end Graffiti199Depleted.WiderOmission
