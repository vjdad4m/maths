import Q8MaskKernel384b

namespace Graffiti384b.Q8
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
private def q8Shape4T2 : Tree := (.split 5 (.tip (.small 1)) (.split 4 (.tip (.small 1)) (.split 8 (.tip (.small 1)) (.split 11 (.tip (.small 1)) (.split 12 (.split 2 (.split 3 (.split 6 (.split 7 (.tip (.small 0)) (.split 9 (.tip (.small 0)) (.split 10 (.tip (.small 0)) (.tip (.unordered 3 0))))) (.split 7 (.split 9 (.tip (.small 0)) (.tip (.unordered 3 0))) (.tip (.unordered 3 1)))) (.split 6 (.split 7 (.split 9 (.tip (.small 0)) (.tip (.cover 0 2 4))) (.split 9 (.tip (.zero 5)) (.tip (.cover 2 3 5)))) (.tip (.cover 0 2 3)))) (.split 3 (.split 6 (.split 7 (.split 9 (.tip (.small 0)) (.split 10 (.tip (.small 0)) (.tip (.unordered 4 0)))) (.tip (.cover 0 2 3))) (.split 7 (.split 9 (.split 10 (.tip (.small 0)) (.tip (.equal 0 1))) (.tip (.unordered 3 1))) (.tip (.unordered 3 1)))) (.tip (.cover 0 1 2)))) (.tip (.cover 0 5 7)))))))
private theorem q8Shape4T2OK : treeOK (forms 4) 0 3 q8Shape4T2=true := by decide

private def q8Shape4T4 : Tree := (.split 4 (.tip (.small 1)) (.split 8 (.tip (.small 1)) (.split 11 (.tip (.small 1)) (.split 12 (.split 2 (.split 3 (.split 6 (.split 7 (.tip (.small 0)) (.split 9 (.tip (.small 0)) (.tip (.cover 0 3 4)))) (.split 7 (.split 9 (.tip (.small 0)) (.split 10 (.tip (.small 0)) (.tip (.unordered 4 0)))) (.tip (.cover 0 1 3)))) (.split 6 (.split 7 (.split 9 (.tip (.small 0)) (.split 10 (.tip (.small 0)) (.tip (.unordered 2 0)))) (.split 9 (.tip (.zero 5)) (.tip (.cover 2 3 5)))) (.tip (.cover 0 2 3)))) (.split 3 (.split 6 (.split 7 (.split 9 (.tip (.small 0)) (.tip (.unordered 2 0))) (.tip (.cover 0 2 3))) (.split 7 (.split 9 (.split 10 (.tip (.small 0)) (.tip (.equal 0 1))) (.tip (.unordered 2 1))) (.tip (.cover 0 1 3)))) (.tip (.unordered 2 1)))) (.tip (.cover 0 5 7))))))
private theorem q8Shape4T4OK : treeOK (forms 4) 2 33 q8Shape4T4=true := by decide

private def q8Shape4T5 : Tree := (.split 4 (.split 8 (.tip (.small 1)) (.split 11 (.tip (.small 1)) (.tip (.unordered 4 1)))) (.split 8 (.split 11 (.tip (.small 1)) (.tip (.unordered 4 1))) (.split 11 (.split 12 (.split 2 (.split 3 (.split 6 (.split 7 (.tip (.equal 2 3)) (.split 9 (.tip (.zero 5)) (.split 10 (.tip (.equal 0 1)) (.tip (.unordered 4 0))))) (.split 7 (.split 9 (.split 10 (.tip (.small 0)) (.tip (.equal 0 1))) (.tip (.unordered 4 1))) (.tip (.cover 0 1 3)))) (.split 6 (.split 7 (.split 9 (.tip (.zero 5)) (.split 10 (.tip (.equal 0 1)) (.tip (.unordered 4 0)))) (.tip (.cover 2 3 5))) (.tip (.cover 0 2 3)))) (.split 3 (.split 6 (.split 7 (.split 9 (.split 10 (.tip (.small 0)) (.tip (.equal 0 1))) (.tip (.unordered 4 1))) (.tip (.cover 0 2 3))) (.tip (.cover 2 3 6))) (.tip (.cover 0 1 2)))) (.split 2 (.split 3 (.split 6 (.split 7 (.tip (.equal 2 3)) (.tip (.cover 2 3 5))) (.tip (.cover 2 3 6))) (.tip (.cover 2 3 5))) (.tip (.cover 2 3 6)))) (.tip (.unordered 4 1)))))
private theorem q8Shape4T5OK : treeOK (forms 4) 34 1 q8Shape4T5=true := by decide

private def q8Shape4T3 : Tree := .split 5 q8Shape4T4 q8Shape4T5
private theorem q8Shape4T3OK : treeOK (forms 4) 2 1 q8Shape4T3=true := by
  change (treeOK (forms 4) 2 (1 ||| 2^5) q8Shape4T4 &&
    treeOK (forms 4) (2 ||| 2^5) 1 q8Shape4T5)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape4T4OK,q8Shape4T5OK⟩

private def q8Shape4T1 : Tree := .split 1 q8Shape4T2 q8Shape4T3
private theorem q8Shape4T1OK : treeOK (forms 4) 0 1 q8Shape4T1=true := by
  change (treeOK (forms 4) 0 (1 ||| 2^1) q8Shape4T2 &&
    treeOK (forms 4) (0 ||| 2^1) 1 q8Shape4T3)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape4T2OK,q8Shape4T3OK⟩

private def q8Shape4T8 : Tree := (.split 4 (.tip (.small 1)) (.split 8 (.tip (.small 1)) (.split 11 (.tip (.small 1)) (.split 12 (.split 2 (.split 3 (.split 6 (.split 7 (.tip (.small 0)) (.split 9 (.tip (.small 0)) (.tip (.cover 0 3 4)))) (.split 7 (.split 9 (.tip (.small 0)) (.split 10 (.tip (.small 0)) (.tip (.equal 0 1)))) (.tip (.unordered 3 1)))) (.split 6 (.split 7 (.split 9 (.tip (.small 0)) (.tip (.cover 0 2 4))) (.tip (.unordered 2 1))) (.split 7 (.split 9 (.split 10 (.tip (.small 0)) (.tip (.equal 0 1))) (.tip (.cover 3 4 6))) (.tip (.unordered 2 1))))) (.split 3 (.split 6 (.split 7 (.split 9 (.tip (.small 0)) (.split 10 (.tip (.small 0)) (.tip (.equal 0 1)))) (.split 9 (.split 10 (.tip (.small 0)) (.tip (.equal 0 1))) (.tip (.cover 2 4 6)))) (.tip (.unordered 2 1))) (.tip (.unordered 2 1)))) (.tip (.cover 0 5 7))))))
private theorem q8Shape4T8OK : treeOK (forms 4) 1 34 q8Shape4T8=true := by decide

private def q8Shape4T9 : Tree := (.split 4 (.split 8 (.tip (.small 1)) (.split 11 (.tip (.small 1)) (.tip (.unordered 3 1)))) (.split 8 (.split 11 (.tip (.small 1)) (.split 12 (.split 2 (.split 3 (.split 6 (.split 7 (.split 9 (.tip (.small 0)) (.split 10 (.tip (.small 0)) (.tip (.equal 0 1)))) (.split 9 (.tip (.zero 5)) (.split 10 (.tip (.equal 0 1)) (.tip (.unordered 3 1))))) (.split 7 (.split 9 (.split 10 (.tip (.small 0)) (.tip (.equal 0 1))) (.tip (.unordered 3 1))) (.tip (.unordered 3 1)))) (.split 6 (.split 7 (.split 9 (.tip (.zero 5)) (.tip (.cover 0 2 4))) (.tip (.unordered 3 1))) (.split 7 (.split 9 (.split 10 (.tip (.equal 0 1)) (.tip (.cover 2 4 5))) (.tip (.unordered 3 1))) (.tip (.unordered 3 1))))) (.split 3 (.split 6 (.split 7 (.split 9 (.split 10 (.tip (.small 0)) (.tip (.equal 0 1))) (.tip (.cover 2 4 6))) (.split 9 (.split 10 (.tip (.equal 0 1)) (.tip (.unordered 3 1))) (.tip (.cover 2 4 6)))) (.tip (.unordered 3 1))) (.tip (.cover 0 1 2)))) (.split 2 (.split 3 (.split 6 (.split 7 (.split 9 (.split 10 (.tip (.small 0)) (.tip (.equal 0 1))) (.tip (.cover 2 4 6))) (.tip (.cover 3 5 7))) (.tip (.cover 3 6 7))) (.tip (.cover 2 4 5))) (.tip (.cover 2 4 6))))) (.split 11 (.tip (.unordered 3 1)) (.tip (.unordered 3 1)))))
private theorem q8Shape4T9OK : treeOK (forms 4) 33 2 q8Shape4T9=true := by decide

private def q8Shape4T7 : Tree := .split 5 q8Shape4T8 q8Shape4T9
private theorem q8Shape4T7OK : treeOK (forms 4) 1 2 q8Shape4T7=true := by
  change (treeOK (forms 4) 1 (2 ||| 2^5) q8Shape4T8 &&
    treeOK (forms 4) (1 ||| 2^5) 2 q8Shape4T9)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape4T8OK,q8Shape4T9OK⟩

private def q8Shape4T11 : Tree := (.split 4 (.split 8 (.tip (.small 1)) (.split 11 (.tip (.small 1)) (.split 12 (.split 2 (.split 3 (.split 6 (.split 7 (.split 9 (.tip (.small 0)) (.split 10 (.tip (.small 0)) (.tip (.equal 0 1)))) (.split 9 (.tip (.zero 5)) (.tip (.cover 0 3 4)))) (.split 7 (.split 9 (.split 10 (.tip (.small 0)) (.tip (.equal 0 1))) (.tip (.cover 3 4 6))) (.tip (.cover 0 1 3)))) (.split 6 (.split 7 (.split 9 (.tip (.zero 5)) (.split 10 (.tip (.equal 0 1)) (.tip (.unordered 2 1)))) (.tip (.unordered 2 1))) (.split 7 (.split 9 (.split 10 (.tip (.equal 0 1)) (.tip (.unordered 2 1))) (.tip (.cover 3 4 6))) (.tip (.unordered 2 1))))) (.split 3 (.split 6 (.split 7 (.split 9 (.split 10 (.tip (.small 0)) (.tip (.equal 0 1))) (.tip (.unordered 2 1))) (.split 9 (.split 10 (.tip (.equal 0 1)) (.tip (.cover 3 4 5))) (.tip (.unordered 2 1)))) (.tip (.unordered 2 1))) (.tip (.unordered 2 1)))) (.split 2 (.split 3 (.split 6 (.split 7 (.split 9 (.split 10 (.tip (.small 0)) (.tip (.equal 0 1))) (.tip (.cover 3 4 6))) (.tip (.cover 3 4 5))) (.tip (.cover 3 4 6))) (.tip (.cover 2 5 7))) (.tip (.cover 2 6 7)))))) (.split 8 (.split 11 (.tip (.small 1)) (.tip (.unordered 2 1))) (.split 11 (.tip (.unordered 2 1)) (.tip (.unordered 2 1)))))
private theorem q8Shape4T11OK : treeOK (forms 4) 3 32 q8Shape4T11=true := by decide

private def q8Shape4T12 : Tree := (.split 4 (.split 8 (.split 11 (.tip (.small 1)) (.tip (.unordered 4 1))) (.split 11 (.tip (.unordered 3 1)) (.tip (.unordered 3 1)))) (.split 8 (.split 11 (.tip (.unordered 2 1)) (.tip (.unordered 2 1))) (.split 11 (.tip (.unordered 2 1)) (.tip (.unordered 2 1)))))
private theorem q8Shape4T12OK : treeOK (forms 4) 35 0 q8Shape4T12=true := by decide

private def q8Shape4T10 : Tree := .split 5 q8Shape4T11 q8Shape4T12
private theorem q8Shape4T10OK : treeOK (forms 4) 3 0 q8Shape4T10=true := by
  change (treeOK (forms 4) 3 (0 ||| 2^5) q8Shape4T11 &&
    treeOK (forms 4) (3 ||| 2^5) 0 q8Shape4T12)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape4T11OK,q8Shape4T12OK⟩

private def q8Shape4T6 : Tree := .split 1 q8Shape4T7 q8Shape4T10
private theorem q8Shape4T6OK : treeOK (forms 4) 1 0 q8Shape4T6=true := by
  change (treeOK (forms 4) 1 (0 ||| 2^1) q8Shape4T7 &&
    treeOK (forms 4) (1 ||| 2^1) 0 q8Shape4T10)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape4T7OK,q8Shape4T10OK⟩

private def q8Shape4T0 : Tree := .split 0 q8Shape4T1 q8Shape4T6
private theorem q8Shape4T0OK : treeOK (forms 4) 0 0 q8Shape4T0=true := by
  change (treeOK (forms 4) 0 (0 ||| 2^0) q8Shape4T1 &&
    treeOK (forms 4) (0 ||| 2^0) 0 q8Shape4T6)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape4T1OK,q8Shape4T6OK⟩


theorem q8Shape4_cover (b : Nat→Bool) (H : Ranked (adj (forms 4) b)) :
    ∃ u v w,Dominates3 (adj (forms 4) b) u v w :=
  checked_tree (forms 4) b H q8Shape4T0 q8Shape4T0OK

#print axioms q8Shape4_cover
end Graffiti384b.Q8
