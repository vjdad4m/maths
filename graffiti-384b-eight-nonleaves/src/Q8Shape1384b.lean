import Q8MaskKernel384b

namespace Graffiti384b.Q8
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
private def q8Shape1T1 : Tree := (.split 14 (.tip (.small 1)) (.split 9 (.tip (.small 0)) (.split 1 (.tip (.small 0)) (.split 2 (.tip (.small 0)) (.split 3 (.tip (.small 1)) (.split 4 (.tip (.small 1)) (.tip (.unordered 2 0))))))))
private theorem q8Shape1T1OK : treeOK (forms 1) 0 1 q8Shape1T1=true := by decide

private def q8Shape1T2 : Tree := (.split 14 (.split 9 (.split 1 (.tip (.small 0)) (.split 2 (.tip (.small 0)) (.split 3 (.tip (.small 1)) (.split 4 (.tip (.small 1)) (.tip (.unordered 2 0)))))) (.split 1 (.split 2 (.tip (.small 0)) (.split 3 (.tip (.small 1)) (.split 4 (.tip (.small 1)) (.tip (.cover 1 2 4))))) (.split 2 (.split 3 (.tip (.small 1)) (.split 4 (.tip (.small 1)) (.tip (.cover 1 2 5)))) (.split 3 (.tip (.small 1)) (.tip (.unordered 2 1)))))) (.split 9 (.split 1 (.tip (.small 0)) (.split 2 (.tip (.small 0)) (.split 3 (.split 4 (.tip (.small 1)) (.tip (.cover 0 2 6))) (.tip (.cover 0 2 7))))) (.split 1 (.split 2 (.tip (.small 0)) (.split 3 (.split 4 (.tip (.small 1)) (.split 5 (.tip (.small 0)) (.tip (.cover 2 4 6)))) (.split 4 (.split 5 (.tip (.small 0)) (.tip (.cover 2 4 7))) (.tip (.unordered 2 0))))) (.split 2 (.split 3 (.split 4 (.tip (.small 1)) (.split 5 (.tip (.small 0)) (.split 6 (.tip (.small 0)) (.tip (.unordered 3 0))))) (.split 4 (.split 5 (.tip (.small 0)) (.split 6 (.tip (.small 0)) (.tip (.unordered 3 0)))) (.tip (.unordered 2 0)))) (.split 3 (.split 4 (.tip (.small 1)) (.tip (.unordered 2 1))) (.tip (.cover 0 2 7)))))))
private theorem q8Shape1T2OK : treeOK (forms 1) 1 0 q8Shape1T2=true := by decide

private def q8Shape1T0 : Tree := .split 0 q8Shape1T1 q8Shape1T2
private theorem q8Shape1T0OK : treeOK (forms 1) 0 0 q8Shape1T0=true := by
  change (treeOK (forms 1) 0 (0 ||| 2^0) q8Shape1T1 &&
    treeOK (forms 1) (0 ||| 2^0) 0 q8Shape1T2)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape1T1OK,q8Shape1T2OK⟩


theorem q8Shape1_cover (b : Nat→Bool) (H : Ranked (adj (forms 1) b)) :
    ∃ u v w,Dominates3 (adj (forms 1) b) u v w :=
  checked_tree (forms 1) b H q8Shape1T0 q8Shape1T0OK

#print axioms q8Shape1_cover
end Graffiti384b.Q8
