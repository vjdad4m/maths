import FragmentChecks
import TriSeparated

namespace Graffiti199Depleted.WiderOmission
namespace TriangleSeparatedFlank2_91088
set_option maxRecDepth 4096
set_option maxHeartbeats 7000000

abbrev e := edgeTriSeparated 2 91088
abbrev P : List ℕ := [0,3,30,48,63,94,286,350]

def singleCover : Cover 11 := (.split 2 (.split 5 (.split 4 (.split 0 (.split 6 (.split 1 (.split 3 (.split 8 (.other 0) (.tree ![0,1,2,8,7,10])) (.tree ![0,1,3,6,10,7])) (.tree ![0,1,2,6,10,7])) (.tree ![2,4,5,6,7,10])) (.split 6 (.split 1 (.tree ![0,1,10,2,6,7]) (.split 3 (.split 8 (.other 3) (.tree ![0,10,8,4,2,5])) (.tree ![0,10,3,4,5,6]))) (.tree ![0,10,6,4,2,5]))) (.split 0 (.split 6 (.tree ![2,4,5,6,10,7]) (.split 1 (.tree ![0,1,2,6,7,10]) (.tree ![0,1,2,9,10,7]))) (.tree ![0,10,4,2,5,9]))) (.split 4 (.split 0 (.split 6 (.tree ![2,4,5,6,10,7]) (.split 1 (.tree ![0,1,2,6,7,10]) (.tree ![0,1,2,9,10,7]))) (.split 6 (.tree ![2,4,5,6,10,7]) (.tree ![0,10,6,4,7,2]))) (.split 0 (.split 6 (.split 1 (.split 3 (.split 8 (.other 48) (.tree ![0,1,2,8,7,10])) (.tree ![0,1,3,6,10,7])) (.tree ![0,1,2,6,10,7])) (.split 1 (.tree ![0,1,2,6,7,10]) (.tree ![0,1,2,9,10,7]))) (.tree ![0,10,4,2,9,7])))) (.split 5 (.split 4 (.tree ![2,4,10,5,9,7]) (.split 0 (.split 6 (.split 1 (.tree ![0,1,2,6,10,7]) (.split 3 (.tree ![0,1,3,6,10,7]) (.split 8 (.other 30) (.other 286)))) (.split 1 (.tree ![0,1,2,9,10,7]) (.split 3 (.tree ![0,1,3,9,10,7]) (.split 8 (.other 94) (.other 350))))) (.tree ![0,10,4,5,9,7]))) (.split 4 (.split 0 (.split 6 (.split 1 (.tree ![0,1,2,6,10,7]) (.tree ![0,1,6,10,7,5])) (.split 1 (.tree ![0,1,6,7,10,5]) (.tree ![0,1,9,10,7,5]))) (.split 6 (.tree ![0,10,2,4,6,7]) (.tree ![0,10,2,5,6,7]))) (.split 0 (.split 6 (.split 1 (.tree ![0,1,2,6,10,7]) (.tree ![0,1,6,10,7,5])) (.split 1 (.tree ![0,1,6,7,10,5]) (.tree ![0,1,9,10,7,5]))) (.split 6 (.split 1 (.tree ![0,1,10,6,5,7]) (.split 3 (.tree ![0,10,4,3,6,7]) (.split 8 (.other 63) (.tree ![0,10,2,5,8,6])))) (.tree ![0,10,2,5,6,7]))))))

private theorem singleValidity : singleCover.Valid (singlePattern e)
    (ProfileKnown (n := 9) P) 640 0 := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · decide +kernel
    · decide +kernel

theorem classified : SingleChecks e (7 : Fin 10) P := certify_single singleValidity

private def left (m : ℕ) : FragmentRoute 9 2 := ([(286,⟨0,3,[.vertex 0,.vertex 1,.vertex 9,.vertex 7,.vertex 8,.across 1 true,.vertex 4,.across 0 false]⟩),(350,⟨0,3,[.vertex 0,.vertex 1,.vertex 9,.vertex 7,.vertex 8,.across 1 true,.vertex 4,.across 0 false]⟩)].lookup m).getD ⟨0,0,[]⟩
private def right (_ : ℕ) : FragmentRoute 9 2 := ⟨0,0,[]⟩
private def pair (a d : ℕ) (b : Bool) : FragmentChoice 9 2 2 :=
  ([((3,286,false),.route ⟨0,3,[.vertex 0,.vertex 1,.vertex 9,.vertex 7,.vertex 8,.across 1 true,.vertex 4,.across 0 false]⟩),((3,286,true),.tree ![0,10,11,4,5,6]),((3,350,false),.route ⟨0,3,[.vertex 0,.vertex 1,.vertex 9,.vertex 7,.vertex 8,.across 1 true,.vertex 4,.across 0 false]⟩),((3,350,true),.tree ![0,10,11,2,6,7]),((63,286,false),.tree ![0,10,4,6,11,7]),((63,286,true),.tree ![0,10,5,11,8,6]),((63,350,false),.tree ![0,10,2,5,11,6]),((63,350,true),.tree ![0,10,5,11,6,7])].lookup (a,d,b)).getD .keep
private def step (_ : ℕ) (_ : Bool) : FragmentChoice 9 2 3 :=
  .keep

def rule : FragmentFlanks 9 2 layoutTriSeparated e seamsTriSeparated (7 : Fin 10) :=
  flanks_from_checks _ _ _ _ P 516 0 false classified
    (by decide +kernel) (by decide +kernel) (lc := left) (rc := right) (pc := pair) (sc := step)
    (by unfold LeftRoutes; decide +kernel)
    (by unfold RightRoutes; decide +kernel)
    (by unfold PairChecks; intro i; fin_cases i <;> decide +kernel)
    (by unfold StepChecks; intro h; exfalso; exact (by decide +kernel : 516 ∉ P) h)

end TriangleSeparatedFlank2_91088
end Graffiti199Depleted.WiderOmission
