import Q8MaskKernel384b

namespace Graffiti384b.Q8
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
private def q8Shape3T1 : Tree := (.split 1 (.split 2 (.split 5 (.tip (.small 0)) (.split 6 (.tip (.small 0)) (.split 9 (.tip (.small 0)) (.tip (.equal 0 1))))) (.split 5 (.split 6 (.tip (.small 0)) (.split 9 (.tip (.small 0)) (.tip (.unordered 5 0)))) (.split 6 (.split 9 (.tip (.small 0)) (.tip (.equal 0 1))) (.split 9 (.tip (.equal 0 1)) (.tip (.unordered 5 0)))))) (.split 2 (.split 5 (.split 6 (.tip (.small 0)) (.split 9 (.tip (.small 0)) (.tip (.equal 0 1)))) (.split 6 (.split 9 (.tip (.small 0)) (.tip (.unordered 4 0))) (.split 9 (.tip (.equal 0 1)) (.tip (.unordered 4 0))))) (.split 5 (.split 6 (.split 9 (.tip (.small 0)) (.tip (.equal 0 1))) (.split 9 (.tip (.equal 0 1)) (.tip (.unordered 5 0)))) (.split 6 (.split 9 (.tip (.equal 0 1)) (.tip (.unordered 4 0))) (.split 9 (.tip (.equal 0 1)) (.tip (.unordered 4 0)))))))
private theorem q8Shape3T1OK : treeOK (forms 3) 0 1 q8Shape3T1=true := by decide

private def q8Shape3T2 : Tree := (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 0)) (.split 9 (.tip (.small 0)) (.tip (.equal 0 1)))) (.split 6 (.split 9 (.tip (.small 0)) (.tip (.equal 0 1))) (.split 9 (.tip (.unordered 3 0)) (.tip (.unordered 3 0))))) (.split 5 (.split 6 (.split 9 (.tip (.small 0)) (.tip (.equal 0 1))) (.split 9 (.tip (.equal 0 1)) (.tip (.unordered 5 0)))) (.split 6 (.split 9 (.tip (.equal 0 1)) (.tip (.equal 0 1))) (.split 9 (.tip (.unordered 3 0)) (.tip (.unordered 3 0)))))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 0)) (.tip (.equal 0 1))) (.split 9 (.tip (.equal 0 1)) (.tip (.equal 0 1)))) (.split 6 (.split 9 (.tip (.equal 0 1)) (.tip (.unordered 4 0))) (.split 9 (.tip (.unordered 3 0)) (.tip (.unordered 3 0))))) (.split 5 (.split 6 (.split 9 (.tip (.unordered 2 0)) (.tip (.unordered 2 0))) (.split 9 (.tip (.unordered 2 0)) (.tip (.unordered 2 0)))) (.split 6 (.split 9 (.tip (.unordered 2 0)) (.tip (.unordered 2 0))) (.split 9 (.tip (.unordered 2 0)) (.tip (.unordered 2 0)))))))
private theorem q8Shape3T2OK : treeOK (forms 3) 1 0 q8Shape3T2=true := by decide

private def q8Shape3T0 : Tree := .split 0 q8Shape3T1 q8Shape3T2
private theorem q8Shape3T0OK : treeOK (forms 3) 0 0 q8Shape3T0=true := by
  change (treeOK (forms 3) 0 (0 ||| 2^0) q8Shape3T1 &&
    treeOK (forms 3) (0 ||| 2^0) 0 q8Shape3T2)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape3T1OK,q8Shape3T2OK⟩


theorem q8Shape3_cover (b : Nat→Bool) (H : Ranked (adj (forms 3) b)) :
    ∃ u v w,Dominates3 (adj (forms 3) b) u v w :=
  checked_tree (forms 3) b H q8Shape3T0 q8Shape3T0OK

#print axioms q8Shape3_cover
end Graffiti384b.Q8
