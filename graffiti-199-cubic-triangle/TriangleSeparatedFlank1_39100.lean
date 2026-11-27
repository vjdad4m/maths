import FragmentChecks
import TriSeparated

namespace Graffiti199Depleted.WiderOmission
namespace TriangleSeparatedFlank1_39100
set_option maxRecDepth 4096
set_option maxHeartbeats 7000000

abbrev e := edgeTriSeparated 1 39100
abbrev P : List ℕ := [0,6,192,387,395,419,427,455]

def singleCover : Cover 11 := (.split 1 (.split 2 (.split 6 (.split 3 (.split 0 (.split 7 (.split 8 (.split 5 (.other 0) (.tree ![0,1,2,5,4,10])) (.tree ![1,2,3,8,4,10])) (.tree ![0,7,3,6,10,4])) (.tree ![0,1,10,2,3,4])) (.split 0 (.tree ![0,1,2,3,4,10]) (.tree ![0,1,10,2,9,4]))) (.split 3 (.split 0 (.split 7 (.tree ![0,7,3,6,4,10]) (.split 8 (.split 5 (.other 192) (.tree ![0,1,2,5,4,10])) (.tree ![1,2,3,8,4,10]))) (.tree ![0,1,10,2,3,4])) (.tree ![1,2,3,4,10,6]))) (.split 6 (.split 3 (.split 0 (.tree ![0,1,2,3,10,4]) (.split 7 (.tree ![0,7,10,3,6,4]) (.tree ![2,10,7,3,6,4]))) (.split 0 (.tree ![0,1,2,9,10,4]) (.tree ![0,10,2,3,4,9]))) (.split 3 (.split 0 (.tree ![0,1,2,3,10,4]) (.tree ![0,1,10,3,6,4])) (.split 0 (.tree ![0,1,3,4,10,6]) (.tree ![0,10,2,3,6,4]))))) (.split 2 (.split 6 (.split 3 (.split 0 (.tree ![0,1,2,3,10,4]) (.split 7 (.tree ![0,7,10,3,6,4]) (.split 8 (.tree ![1,2,3,8,10,4]) (.split 5 (.other 387) (.other 419))))) (.split 0 (.tree ![0,1,2,9,10,4]) (.split 7 (.tree ![0,7,10,6,9,4]) (.split 8 (.tree ![1,2,8,9,10,4]) (.split 5 (.other 395) (.other 427)))))) (.tree ![1,2,9,10,4,6])) (.split 6 (.split 3 (.split 0 (.split 7 (.split 8 (.split 5 (.other 6) (.tree ![0,7,5,4,10,2])) (.tree ![2,10,8,7,3,4])) (.tree ![0,7,3,6,10,4])) (.split 7 (.tree ![0,7,10,3,6,4]) (.tree ![2,10,7,3,6,4]))) (.split 0 (.split 7 (.tree ![0,7,3,4,10,2]) (.tree ![0,7,9,10,4,2])) (.tree ![0,10,2,3,4,9]))) (.split 3 (.split 0 (.tree ![0,1,3,10,4,6]) (.split 7 (.tree ![0,7,10,3,2,4]) (.split 8 (.tree ![1,3,8,10,4,6]) (.split 5 (.other 455) (.tree ![0,10,2,5,6,3]))))) (.split 0 (.tree ![0,1,9,10,4,6]) (.tree ![0,10,2,3,6,4]))))))

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
  ([((387,387,false),.tree ![1,2,3,10,11,4]),((387,387,true),.keep),((387,395,false),.tree ![1,2,5,10,11,4]),((387,395,true),.route ⟨0,3,[.vertex 0,.vertex 8,.vertex 7,.across 1 true,.vertex 4,.vertex 9,.vertex 1,.across 0 false]⟩),((387,419,false),.tree ![1,2,3,10,11,4]),((387,419,true),.route ⟨0,5,[.vertex 0,.vertex 8,.vertex 1,.across 0 false,.vertex 4,.vertex 9,.vertex 7,.across 1 true]⟩),((387,427,false),.tree ![1,2,9,10,11,4]),((387,427,true),.route ⟨0,5,[.vertex 0,.vertex 8,.vertex 1,.across 0 false,.vertex 4,.vertex 9,.vertex 7,.across 1 true]⟩),((387,455,false),.tree ![1,3,10,11,4,6]),((387,455,true),.route ⟨0,6,[.vertex 0,.vertex 8,.vertex 1,.across 0 false,.vertex 4,.vertex 9,.vertex 7,.across 1 false]⟩),((395,387,false),.tree ![1,2,5,10,11,4]),((395,387,true),.route ⟨3,8,[.across 0 true,.vertex 1,.vertex 9,.vertex 4,.across 1 false,.vertex 7,.vertex 0,.vertex 8]⟩),((395,395,false),.tree ![1,2,5,10,11,4]),((395,395,true),.route ⟨0,3,[.vertex 0,.vertex 8,.vertex 7,.across 1 true,.vertex 4,.vertex 9,.vertex 1,.across 0 false]⟩),((395,419,false),.tree ![1,2,9,10,11,4]),((395,419,true),.route ⟨0,5,[.vertex 0,.vertex 8,.vertex 1,.across 0 false,.vertex 4,.vertex 9,.vertex 7,.across 1 true]⟩),((395,427,false),.tree ![1,2,9,10,11,4]),((395,427,true),.route ⟨0,5,[.vertex 0,.vertex 8,.vertex 1,.across 0 false,.vertex 4,.vertex 9,.vertex 7,.across 1 true]⟩),((395,455,false),.tree ![0,10,11,3,2,4]),((395,455,true),.tree ![2,11,6,10,3,4]),((419,387,false),.tree ![1,2,3,10,11,4]),((419,387,true),.route ⟨5,8,[.across 1 false,.vertex 7,.vertex 9,.vertex 4,.across 0 true,.vertex 1,.vertex 0,.vertex 8]⟩),((419,395,false),.tree ![1,2,9,10,11,4]),((419,395,true),.route ⟨0,3,[.vertex 0,.vertex 8,.vertex 7,.across 1 true,.vertex 4,.vertex 9,.vertex 1,.across 0 false]⟩),((419,419,false),.tree ![1,2,3,10,11,4]),((419,419,true),.route ⟨0,5,[.vertex 0,.vertex 8,.vertex 1,.across 0 false,.vertex 4,.vertex 9,.vertex 7,.across 1 true]⟩),((419,427,false),.tree ![1,2,9,10,11,4]),((419,427,true),.route ⟨0,5,[.vertex 0,.vertex 8,.vertex 1,.across 0 false,.vertex 4,.vertex 9,.vertex 7,.across 1 true]⟩),((419,455,false),.tree ![0,10,11,5,2,3]),((419,455,true),.tree ![2,11,6,10,5,3]),((427,387,false),.tree ![1,2,9,10,11,4]),((427,387,true),.route ⟨3,8,[.across 0 true,.vertex 1,.vertex 9,.vertex 4,.across 1 false,.vertex 7,.vertex 0,.vertex 8]⟩),((427,395,false),.tree ![1,2,9,10,11,4]),((427,395,true),.route ⟨0,3,[.vertex 0,.vertex 8,.vertex 7,.across 1 true,.vertex 4,.vertex 9,.vertex 1,.across 0 false]⟩),((427,419,false),.tree ![1,2,9,10,11,4]),((427,419,true),.route ⟨0,5,[.vertex 0,.vertex 8,.vertex 1,.across 0 false,.vertex 4,.vertex 9,.vertex 7,.across 1 true]⟩),((427,427,false),.tree ![1,2,9,10,11,4]),((427,427,true),.route ⟨0,5,[.vertex 0,.vertex 8,.vertex 1,.across 0 false,.vertex 4,.vertex 9,.vertex 7,.across 1 true]⟩),((427,455,false),.tree ![0,10,11,3,2,4]),((427,455,true),.tree ![2,11,6,10,3,4]),((455,387,false),.tree ![1,3,10,11,4,6]),((455,387,true),.route ⟨2,8,[.across 0 false,.vertex 1,.vertex 9,.vertex 4,.across 1 false,.vertex 7,.vertex 0,.vertex 8]⟩),((455,395,false),.tree ![0,10,11,2,3,4]),((455,395,true),.tree ![2,10,6,11,3,4]),((455,419,false),.tree ![0,10,11,2,5,3]),((455,419,true),.tree ![2,10,6,11,5,3]),((455,427,false),.tree ![0,10,11,2,3,4]),((455,427,true),.tree ![2,10,6,11,3,4]),((455,455,false),.route ⟨0,6,[.vertex 0,.vertex 8,.vertex 1,.across 0 false,.vertex 4,.vertex 9,.vertex 7,.across 1 false]⟩),((455,455,true),.route ⟨0,6,[.vertex 0,.vertex 8,.vertex 1,.across 0 false,.vertex 4,.vertex 9,.vertex 7,.across 1 false]⟩)].lookup (a,d,b)).getD .keep
private def step (a : ℕ) (b : Bool) : FragmentChoice 9 2 3 :=
  ([((0,false),.tree ![1,2,3,10,4,12]),((0,true),.tree ![1,2,3,10,4,12]),((6,false),.tree ![2,12,10,7,3,4]),((6,true),.tree ![2,12,10,7,3,4]),((192,false),.tree ![1,2,3,10,4,12]),((192,true),.tree ![1,2,3,10,4,12]),((387,false),.tree ![1,2,3,11,12,4]),((387,true),.keep),((395,false),.tree ![1,2,5,11,12,4]),((395,true),.route ⟨3,8,[.across 0 true,.vertex 1,.vertex 9,.vertex 4,.across 1 false,.vertex 7,.vertex 0,.vertex 8]⟩),((419,false),.tree ![1,2,3,11,12,4]),((419,true),.route ⟨5,8,[.across 1 false,.vertex 7,.vertex 9,.vertex 4,.across 0 true,.vertex 1,.vertex 0,.vertex 8]⟩),((427,false),.tree ![1,2,9,11,12,4]),((427,true),.route ⟨3,8,[.across 0 true,.vertex 1,.vertex 9,.vertex 4,.across 1 false,.vertex 7,.vertex 0,.vertex 8]⟩),((455,false),.tree ![1,3,11,12,4,6]),((455,true),.route ⟨2,8,[.across 0 false,.vertex 1,.vertex 9,.vertex 4,.across 1 false,.vertex 7,.vertex 0,.vertex 8]⟩)].lookup (a,b)).getD .keep

def rule : FragmentFlanks 9 2 layoutTriSeparated e seamsTriSeparated (4 : Fin 10) :=
  flanks_from_checks _ _ _ _ P 387 387 true classified
    (by decide +kernel) (by decide +kernel) (lc := left) (rc := right) (pc := pair) (sc := step)
    (by unfold LeftRoutes; decide +kernel)
    (by unfold RightRoutes; decide +kernel)
    (by unfold PairChecks; intro i; fin_cases i <;> decide +kernel)
    (by unfold StepChecks; intro _ _ i; fin_cases i <;> decide +kernel)

end TriangleSeparatedFlank1_39100
end Graffiti199Depleted.WiderOmission
