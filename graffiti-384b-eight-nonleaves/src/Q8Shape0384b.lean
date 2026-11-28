import Q8MaskKernel384b

namespace Graffiti384b.Q8
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
private def q8Shape0T2 : Tree := (.split 2 (.split 5 (.tip (.small 0)) (.split 6 (.tip (.small 0)) (.split 9 (.tip (.small 0)) (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2))))))) (.split 5 (.split 6 (.tip (.small 0)) (.split 9 (.tip (.small 0)) (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2)))))) (.split 6 (.split 9 (.tip (.small 0)) (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2))))) (.split 9 (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2)))) (.split 3 (.tip (.unordered 5 0)) (.split 4 (.tip (.unordered 5 1)) (.tip (.cover 0 1 2))))))))
private theorem q8Shape0T2OK : treeOK (forms 0) 0 3 q8Shape0T2=true := by decide

private def q8Shape0T4 : Tree := (.split 5 (.split 6 (.tip (.small 0)) (.split 9 (.tip (.small 0)) (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2)))))) (.split 6 (.split 9 (.tip (.small 0)) (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2))))) (.split 9 (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2)))) (.split 3 (.tip (.unordered 4 0)) (.split 4 (.tip (.unordered 4 1)) (.tip (.cover 0 1 2)))))))
private theorem q8Shape0T4OK : treeOK (forms 0) 2 5 q8Shape0T4=true := by decide

private def q8Shape0T5 : Tree := (.split 5 (.split 6 (.split 9 (.tip (.small 0)) (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.unordered 2 0))))) (.split 9 (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2)))) (.split 3 (.tip (.unordered 5 0)) (.split 4 (.tip (.unordered 5 1)) (.tip (.cover 0 1 2)))))) (.split 6 (.split 9 (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2)))) (.split 3 (.tip (.unordered 4 0)) (.split 4 (.tip (.unordered 4 1)) (.tip (.cover 0 1 2))))) (.split 9 (.split 3 (.split 4 (.split 7 (.tip (.small 0)) (.split 8 (.tip (.small 1)) (.tip (.cover 0 1 3)))) (.split 7 (.tip (.small 0)) (.tip (.cover 0 3 7)))) (.split 4 (.split 7 (.split 8 (.tip (.small 1)) (.tip (.cover 0 2 7))) (.tip (.cover 2 3 7))) (.tip (.cover 0 1 2)))) (.split 3 (.tip (.unordered 4 0)) (.split 4 (.tip (.unordered 4 1)) (.tip (.cover 0 1 2)))))))
private theorem q8Shape0T5OK : treeOK (forms 0) 6 1 q8Shape0T5=true := by decide

private def q8Shape0T3 : Tree := .split 2 q8Shape0T4 q8Shape0T5
private theorem q8Shape0T3OK : treeOK (forms 0) 2 1 q8Shape0T3=true := by
  change (treeOK (forms 0) 2 (1 ||| 2^2) q8Shape0T4 &&
    treeOK (forms 0) (2 ||| 2^2) 1 q8Shape0T5)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape0T4OK,q8Shape0T5OK⟩

private def q8Shape0T1 : Tree := .split 1 q8Shape0T2 q8Shape0T3
private theorem q8Shape0T1OK : treeOK (forms 0) 0 1 q8Shape0T1=true := by
  change (treeOK (forms 0) 0 (1 ||| 2^1) q8Shape0T2 &&
    treeOK (forms 0) (0 ||| 2^1) 1 q8Shape0T3)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape0T2OK,q8Shape0T3OK⟩

private def q8Shape0T8 : Tree := (.split 5 (.split 6 (.tip (.small 0)) (.split 9 (.tip (.small 0)) (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2)))))) (.split 6 (.split 9 (.tip (.small 0)) (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2))))) (.split 9 (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2)))) (.split 3 (.tip (.unordered 3 0)) (.split 4 (.tip (.unordered 3 1)) (.tip (.cover 0 1 2)))))))
private theorem q8Shape0T8OK : treeOK (forms 0) 1 6 q8Shape0T8=true := by decide

private def q8Shape0T9 : Tree := (.split 5 (.split 6 (.split 9 (.tip (.small 0)) (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2))))) (.split 9 (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.unordered 2 0)))) (.split 3 (.tip (.unordered 5 0)) (.split 4 (.tip (.unordered 5 1)) (.tip (.cover 0 1 2)))))) (.split 6 (.split 9 (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2)))) (.split 3 (.split 4 (.split 7 (.tip (.small 0)) (.split 8 (.tip (.small 1)) (.tip (.cover 0 1 3)))) (.split 7 (.tip (.small 0)) (.split 8 (.split 10 (.tip (.small 0)) (.tip (.cover 0 4 7))) (.tip (.unordered 3 0))))) (.split 4 (.split 7 (.split 8 (.tip (.small 1)) (.split 10 (.tip (.small 0)) (.tip (.cover 2 4 7)))) (.split 8 (.tip (.small 1)) (.tip (.unordered 3 1)))) (.tip (.cover 0 1 2))))) (.split 9 (.split 3 (.tip (.unordered 3 0)) (.split 4 (.tip (.unordered 3 1)) (.tip (.cover 0 1 2)))) (.split 3 (.tip (.unordered 3 0)) (.split 4 (.tip (.unordered 3 1)) (.tip (.cover 0 1 2)))))))
private theorem q8Shape0T9OK : treeOK (forms 0) 5 2 q8Shape0T9=true := by decide

private def q8Shape0T7 : Tree := .split 2 q8Shape0T8 q8Shape0T9
private theorem q8Shape0T7OK : treeOK (forms 0) 1 2 q8Shape0T7=true := by
  change (treeOK (forms 0) 1 (2 ||| 2^2) q8Shape0T8 &&
    treeOK (forms 0) (1 ||| 2^2) 2 q8Shape0T9)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape0T8OK,q8Shape0T9OK⟩

private def q8Shape0T11 : Tree := (.split 5 (.split 6 (.split 9 (.tip (.small 0)) (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2))))) (.split 9 (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2)))) (.split 3 (.split 4 (.split 7 (.tip (.small 0)) (.split 8 (.tip (.small 1)) (.tip (.cover 0 1 3)))) (.split 7 (.tip (.small 0)) (.split 8 (.split 10 (.tip (.small 0)) (.tip (.cover 3 4 7))) (.tip (.unordered 3 0))))) (.split 4 (.split 7 (.split 8 (.tip (.small 1)) (.split 10 (.tip (.small 0)) (.tip (.cover 0 4 7)))) (.split 8 (.tip (.small 1)) (.tip (.unordered 3 1)))) (.tip (.cover 0 1 2)))))) (.split 6 (.split 9 (.split 3 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.unordered 2 0)))) (.split 3 (.tip (.unordered 4 0)) (.split 4 (.tip (.unordered 4 1)) (.tip (.cover 0 1 2))))) (.split 9 (.split 3 (.tip (.unordered 3 0)) (.split 4 (.tip (.unordered 3 1)) (.tip (.cover 0 1 2)))) (.split 3 (.tip (.unordered 3 0)) (.split 4 (.tip (.unordered 3 1)) (.tip (.cover 0 1 2)))))))
private theorem q8Shape0T11OK : treeOK (forms 0) 3 4 q8Shape0T11=true := by decide

private def q8Shape0T12 : Tree := (.split 5 (.split 6 (.split 9 (.split 3 (.tip (.small 0)) (.tip (.unordered 2 0))) (.split 3 (.tip (.unordered 2 0)) (.tip (.unordered 2 0)))) (.split 9 (.split 3 (.tip (.unordered 2 0)) (.tip (.unordered 2 0))) (.split 3 (.tip (.unordered 2 0)) (.tip (.unordered 2 0))))) (.split 6 (.split 9 (.split 3 (.tip (.unordered 2 0)) (.tip (.unordered 2 0))) (.split 3 (.tip (.unordered 2 0)) (.tip (.unordered 2 0)))) (.split 9 (.split 3 (.tip (.unordered 2 0)) (.tip (.unordered 2 0))) (.split 3 (.tip (.unordered 2 0)) (.tip (.unordered 2 0))))))
private theorem q8Shape0T12OK : treeOK (forms 0) 7 0 q8Shape0T12=true := by decide

private def q8Shape0T10 : Tree := .split 2 q8Shape0T11 q8Shape0T12
private theorem q8Shape0T10OK : treeOK (forms 0) 3 0 q8Shape0T10=true := by
  change (treeOK (forms 0) 3 (0 ||| 2^2) q8Shape0T11 &&
    treeOK (forms 0) (3 ||| 2^2) 0 q8Shape0T12)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape0T11OK,q8Shape0T12OK⟩

private def q8Shape0T6 : Tree := .split 1 q8Shape0T7 q8Shape0T10
private theorem q8Shape0T6OK : treeOK (forms 0) 1 0 q8Shape0T6=true := by
  change (treeOK (forms 0) 1 (0 ||| 2^1) q8Shape0T7 &&
    treeOK (forms 0) (1 ||| 2^1) 0 q8Shape0T10)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape0T7OK,q8Shape0T10OK⟩

private def q8Shape0T0 : Tree := .split 0 q8Shape0T1 q8Shape0T6
private theorem q8Shape0T0OK : treeOK (forms 0) 0 0 q8Shape0T0=true := by
  change (treeOK (forms 0) 0 (0 ||| 2^0) q8Shape0T1 &&
    treeOK (forms 0) (0 ||| 2^0) 0 q8Shape0T6)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape0T1OK,q8Shape0T6OK⟩


theorem q8Shape0_cover (b : Nat→Bool) (H : Ranked (adj (forms 0) b)) :
    ∃ u v w,Dominates3 (adj (forms 0) b) u v w :=
  checked_tree (forms 0) b H q8Shape0T0 q8Shape0T0OK

#print axioms q8Shape0_cover
end Graffiti384b.Q8
