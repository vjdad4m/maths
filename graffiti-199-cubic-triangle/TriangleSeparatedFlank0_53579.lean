import FragmentChecks
import TriSeparated

namespace Graffiti199Depleted.WiderOmission
namespace TriangleSeparatedFlank0_53579
set_option maxRecDepth 4096
set_option maxHeartbeats 7000000

abbrev e := edgeTriSeparated 0 53579
abbrev P : List ℕ := [0,24,240,241,244,245,384,504]

def singleCover : Cover 11 := (.split 4 (.split 0 (.split 5 (.split 3 (.split 8 (.split 6 (.split 7 (.split 2 (.other 0) (.tree ![1,2,4,10,3,5])) (.tree ![0,1,7,5,8,10])) (.tree ![0,1,4,3,6,10])) (.split 6 (.split 7 (.tree ![0,1,7,5,8,10]) (.split 2 (.other 384) (.tree ![1,2,4,10,3,5]))) (.tree ![0,1,4,3,6,10]))) (.tree ![0,1,4,3,5,10])) (.split 3 (.tree ![0,1,4,3,5,10]) (.split 8 (.split 6 (.tree ![0,1,4,3,6,10]) (.split 7 (.tree ![0,1,7,5,10,3]) (.tree ![0,1,7,8,10,3]))) (.tree ![0,1,4,3,10,8])))) (.split 5 (.split 3 (.tree ![0,1,4,10,3,5]) (.tree ![1,9,4,3,5,10])) (.split 3 (.tree ![1,9,4,3,5,10]) (.tree ![0,1,10,9,3,5])))) (.split 0 (.split 5 (.split 3 (.tree ![0,1,4,3,5,10]) (.split 8 (.split 6 (.split 7 (.split 2 (.other 24) (.tree ![1,2,7,10,5,3])) (.tree ![0,1,7,5,8,10])) (.split 7 (.tree ![0,1,7,6,10,3]) (.tree ![0,1,7,5,8,10]))) (.tree ![0,1,4,5,10,8]))) (.split 3 (.split 8 (.split 6 (.tree ![0,1,4,3,6,10]) (.split 7 (.tree ![0,1,7,5,8,10]) (.split 2 (.other 240) (.other 244)))) (.tree ![0,1,4,3,10,8])) (.split 8 (.split 6 (.split 7 (.tree ![0,1,7,5,10,3]) (.tree ![0,1,7,6,10,3])) (.split 7 (.tree ![0,1,7,5,10,3]) (.tree ![0,1,7,8,10,3]))) (.split 6 (.split 7 (.tree ![0,1,7,5,10,3]) (.tree ![0,1,7,6,10,3])) (.split 7 (.tree ![0,1,7,5,10,3]) (.split 2 (.other 504) (.tree ![0,2,10,3,5,8]))))))) (.split 5 (.split 3 (.tree ![1,9,4,3,5,10]) (.split 8 (.split 6 (.split 7 (.tree ![0,1,7,10,5,3]) (.tree ![1,9,7,5,10,3])) (.tree ![0,1,10,3,6,5])) (.split 6 (.split 7 (.tree ![0,1,7,10,5,3]) (.tree ![1,9,7,5,10,3])) (.tree ![0,1,10,3,6,5])))) (.split 3 (.split 8 (.split 6 (.tree ![1,9,4,3,6,10]) (.split 7 (.tree ![1,9,7,5,8,10]) (.split 2 (.other 241) (.other 245)))) (.tree ![1,9,4,3,10,8])) (.tree ![0,1,10,9,3,5])))))

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
private def right (m : ℕ) : FragmentRoute 9 2 := ([(241,⟨5,8,[.across 1 false,.vertex 4,.across 0 true,.vertex 0,.vertex 1,.vertex 9,.vertex 7,.vertex 8]⟩),(245,⟨5,8,[.across 1 false,.vertex 4,.across 0 true,.vertex 0,.vertex 1,.vertex 9,.vertex 7,.vertex 8]⟩)].lookup m).getD ⟨0,0,[]⟩
private def pair (a d : ℕ) (b : Bool) : FragmentChoice 9 2 2 :=
  ([((241,384,false),.route ⟨5,8,[.across 1 false,.vertex 4,.across 0 true,.vertex 0,.vertex 1,.vertex 9,.vertex 7,.vertex 8]⟩),((241,384,true),.tree ![1,2,4,3,10,11]),((241,504,false),.tree ![0,1,10,5,11,3]),((241,504,true),.tree ![0,1,10,11,3,8]),((245,384,false),.route ⟨5,8,[.across 1 false,.vertex 4,.across 0 true,.vertex 0,.vertex 1,.vertex 9,.vertex 7,.vertex 8]⟩),((245,384,true),.tree ![0,1,10,5,11,8]),((245,504,false),.tree ![0,1,10,5,11,3]),((245,504,true),.tree ![0,1,10,11,3,8])].lookup (a,d,b)).getD .keep
private def step (_ : ℕ) (_ : Bool) : FragmentChoice 9 2 3 :=
  .keep

def rule : FragmentFlanks 9 2 layoutTriSeparated e seamsTriSeparated (1 : Fin 10) :=
  flanks_from_checks _ _ _ _ P 516 0 false classified
    (by decide +kernel) (by decide +kernel) (lc := left) (rc := right) (pc := pair) (sc := step)
    (by unfold LeftRoutes; decide +kernel)
    (by unfold RightRoutes; decide +kernel)
    (by unfold PairChecks; intro i; fin_cases i <;> decide +kernel)
    (by unfold StepChecks; intro h; exfalso; exact (by decide +kernel : 516 ∉ P) h)

end TriangleSeparatedFlank0_53579
end Graffiti199Depleted.WiderOmission
