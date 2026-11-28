import Q8MaskKernel384b

namespace Graffiti384b.Q8
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
private def q8Shape2T1 : Tree := (.split 1 (.split 5 (.tip (.small 0)) (.split 2 (.tip (.small 0)) (.split 3 (.tip (.small 1)) (.split 6 (.tip (.small 0)) (.split 7 (.tip (.small 1)) (.split 9 (.tip (.small 0)) (.split 10 (.tip (.small 1)) (.tip (.unordered 3 0))))))))) (.split 5 (.split 2 (.tip (.small 0)) (.split 3 (.tip (.small 1)) (.split 6 (.tip (.small 0)) (.split 7 (.tip (.small 1)) (.split 9 (.tip (.small 0)) (.split 10 (.tip (.small 1)) (.tip (.unordered 2 0)))))))) (.split 2 (.split 3 (.split 6 (.tip (.small 0)) (.split 7 (.tip (.small 1)) (.split 9 (.tip (.small 0)) (.tip (.unordered 4 0))))) (.split 6 (.tip (.small 0)) (.split 7 (.split 9 (.tip (.small 0)) (.tip (.unordered 4 0))) (.split 9 (.tip (.small 0)) (.tip (.unordered 4 0)))))) (.split 3 (.split 6 (.split 7 (.tip (.small 1)) (.split 9 (.tip (.small 0)) (.tip (.unordered 4 0)))) (.split 7 (.tip (.small 1)) (.split 9 (.split 10 (.tip (.small 1)) (.tip (.unordered 4 0))) (.tip (.unordered 4 0))))) (.split 6 (.split 7 (.split 9 (.tip (.small 0)) (.tip (.unordered 4 0))) (.split 9 (.tip (.small 0)) (.tip (.unordered 4 0)))) (.split 7 (.split 9 (.split 10 (.tip (.small 1)) (.tip (.unordered 4 0))) (.tip (.unordered 4 0))) (.tip (.cover 2 3 7))))))))
private theorem q8Shape2T1OK : treeOK (forms 2) 0 1 q8Shape2T1=true := by decide

private def q8Shape2T3 : Tree := (.split 5 (.split 2 (.tip (.small 0)) (.split 3 (.tip (.small 1)) (.split 6 (.tip (.small 0)) (.split 7 (.tip (.small 1)) (.tip (.unordered 2 0)))))) (.split 2 (.split 3 (.split 6 (.tip (.small 0)) (.split 7 (.tip (.small 1)) (.tip (.unordered 3 0)))) (.split 6 (.tip (.small 0)) (.split 7 (.split 9 (.tip (.small 0)) (.tip (.unordered 3 0))) (.tip (.unordered 3 0))))) (.split 3 (.split 6 (.split 7 (.tip (.small 1)) (.split 9 (.tip (.small 0)) (.split 10 (.tip (.small 1)) (.tip (.unordered 3 0))))) (.tip (.unordered 3 1))) (.split 6 (.split 7 (.split 9 (.tip (.small 0)) (.split 10 (.tip (.small 1)) (.tip (.equal 0 1)))) (.tip (.unordered 3 0))) (.split 7 (.tip (.unordered 3 1)) (.tip (.unordered 3 0)))))))
private theorem q8Shape2T3OK : treeOK (forms 2) 1 2 q8Shape2T3=true := by decide

private def q8Shape2T4 : Tree := (.split 5 (.split 2 (.split 3 (.split 6 (.tip (.small 0)) (.split 7 (.tip (.small 1)) (.split 9 (.tip (.small 0)) (.split 10 (.tip (.small 1)) (.tip (.equal 0 1)))))) (.split 6 (.tip (.small 0)) (.split 7 (.split 9 (.tip (.small 0)) (.split 10 (.tip (.small 1)) (.tip (.unordered 2 0)))) (.tip (.unordered 2 0))))) (.split 3 (.split 6 (.split 7 (.tip (.small 1)) (.split 9 (.tip (.small 0)) (.tip (.unordered 2 0)))) (.tip (.unordered 2 1))) (.split 6 (.tip (.unordered 2 0)) (.tip (.unordered 2 0))))) (.split 2 (.split 3 (.split 6 (.split 7 (.split 9 (.tip (.small 0)) (.tip (.unordered 4 0))) (.tip (.unordered 3 0))) (.split 7 (.tip (.unordered 3 1)) (.tip (.unordered 3 0)))) (.split 6 (.tip (.unordered 2 0)) (.split 7 (.split 9 (.tip (.unordered 2 0)) (.tip (.unordered 3 0))) (.tip (.unordered 2 0))))) (.split 3 (.split 6 (.split 7 (.tip (.unordered 2 1)) (.split 9 (.tip (.unordered 2 0)) (.tip (.unordered 2 0)))) (.tip (.unordered 2 1))) (.split 6 (.tip (.unordered 2 0)) (.tip (.unordered 2 0))))))
private theorem q8Shape2T4OK : treeOK (forms 2) 3 0 q8Shape2T4=true := by decide

private def q8Shape2T2 : Tree := .split 1 q8Shape2T3 q8Shape2T4
private theorem q8Shape2T2OK : treeOK (forms 2) 1 0 q8Shape2T2=true := by
  change (treeOK (forms 2) 1 (0 ||| 2^1) q8Shape2T3 &&
    treeOK (forms 2) (1 ||| 2^1) 0 q8Shape2T4)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape2T3OK,q8Shape2T4OK⟩

private def q8Shape2T0 : Tree := .split 0 q8Shape2T1 q8Shape2T2
private theorem q8Shape2T0OK : treeOK (forms 2) 0 0 q8Shape2T0=true := by
  change (treeOK (forms 2) 0 (0 ||| 2^0) q8Shape2T1 &&
    treeOK (forms 2) (0 ||| 2^0) 0 q8Shape2T2)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape2T1OK,q8Shape2T2OK⟩


theorem q8Shape2_cover (b : Nat→Bool) (H : Ranked (adj (forms 2) b)) :
    ∃ u v w,Dominates3 (adj (forms 2) b) u v w :=
  checked_tree (forms 2) b H q8Shape2T0 q8Shape2T0OK

#print axioms q8Shape2_cover
end Graffiti384b.Q8
