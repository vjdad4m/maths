import Q8MaskKernel384b

namespace Graffiti384b.Q8
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
private def q8Shape7T5 : Tree := (.split 10 (.split 11 (.split 12 (.tip (.zero 6)) (.split 13 (.tip (.zero 7)) (.tip (.equal 6 7)))) (.split 12 (.tip (.zero 6)) (.split 13 (.tip (.equal 6 7)) (.tip (.cover 0 1 5))))) (.split 11 (.split 12 (.split 13 (.tip (.zero 7)) (.tip (.equal 6 7))) (.split 13 (.tip (.zero 7)) (.tip (.cover 0 1 5)))) (.tip (.cover 0 1 4))))
private theorem q8Shape7T5OK : treeOK (forms 7) 0 16792 q8Shape7T5=true := by decide

private def q8Shape7T7 : Tree := (.split 11 (.split 12 (.tip (.zero 6)) (.split 13 (.tip (.equal 6 7)) (.tip (.cover 0 1 5)))) (.split 12 (.tip (.zero 6)) (.split 13 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.tip (.cover 0 5 7))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.cover 0 4 5))) (.tip (.equal 2 7))) (.tip (.cover 0 5 7)))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.equal 3 5)))) (.tip (.equal 2 7))) (.tip (.cover 0 5 7))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 3 5))) (.tip (.cover 3 4 6))) (.tip (.cover 0 3 5))) (.tip (.cover 0 5 7))))) (.tip (.cover 0 1 5)))))
private theorem q8Shape7T7OK : treeOK (forms 7) 256 17560 q8Shape7T7=true := by decide

private def q8Shape7T8 : Tree := (.split 11 (.split 12 (.split 13 (.tip (.equal 6 7)) (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.split 5 (.split 6 (.tip (.small 1)) (.tip (.unordered 5 1))) (.tip (.cover 0 4 5)))) (.tip (.cover 0 4 7))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.unordered 3 1))) (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 3 4))) (.tip (.unordered 3 1)))) (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 3 4))) (.tip (.unordered 3 1))) (.tip (.cover 3 5 6)))) (.tip (.cover 0 4 7))))) (.split 13 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.split 5 (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.unordered 5 1)))) (.tip (.cover 0 3 5)))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.cover 0 3 4))) (.split 6 (.split 9 (.tip (.small 1)) (.tip (.unordered 4 1))) (.tip (.cover 0 3 4)))) (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.unordered 4 1))) (.tip (.cover 4 5 7))) (.tip (.cover 4 5 7))))) (.tip (.cover 0 3 6))) (.tip (.cover 0 1 5)))) (.tip (.cover 0 1 4)))
private theorem q8Shape7T8OK : treeOK (forms 7) 1280 16536 q8Shape7T8=true := by decide

private def q8Shape7T6 : Tree := .split 10 q8Shape7T7 q8Shape7T8
private theorem q8Shape7T6OK : treeOK (forms 7) 256 16536 q8Shape7T6=true := by
  change (treeOK (forms 7) 256 (16536 ||| 2^10) q8Shape7T7 &&
    treeOK (forms 7) (256 ||| 2^10) 16536 q8Shape7T8)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T7OK,q8Shape7T8OK⟩

private def q8Shape7T4 : Tree := .split 8 q8Shape7T5 q8Shape7T6
private theorem q8Shape7T4OK : treeOK (forms 7) 0 16536 q8Shape7T4=true := by
  change (treeOK (forms 7) 0 (16536 ||| 2^8) q8Shape7T5 &&
    treeOK (forms 7) (0 ||| 2^8) 16536 q8Shape7T6)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T5OK,q8Shape7T6OK⟩

private def q8Shape7T11 : Tree := (.split 11 (.split 12 (.split 13 (.tip (.zero 7)) (.tip (.equal 6 7))) (.split 13 (.tip (.zero 7)) (.tip (.cover 0 1 5)))) (.split 12 (.split 13 (.tip (.equal 6 7)) (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.split 5 (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.unordered 5 1)))) (.tip (.cover 0 3 5)))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.cover 0 3 4))) (.split 6 (.split 9 (.tip (.small 1)) (.tip (.unordered 4 1))) (.tip (.cover 0 3 4)))) (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.unordered 4 1))) (.tip (.cover 4 5 6))) (.tip (.cover 4 5 6))))) (.tip (.cover 0 3 7)))) (.split 13 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.split 5 (.split 6 (.tip (.small 1)) (.tip (.unordered 5 1))) (.tip (.cover 0 4 5)))) (.tip (.cover 0 4 6))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.unordered 3 1))) (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 3 4))) (.tip (.unordered 3 1)))) (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 3 4))) (.tip (.unordered 3 1))) (.tip (.cover 3 5 7)))) (.tip (.cover 0 4 6)))) (.tip (.cover 0 1 5)))))
private theorem q8Shape7T11OK : treeOK (forms 7) 128 17688 q8Shape7T11=true := by decide

private def q8Shape7T12 : Tree := (.split 11 (.split 12 (.split 13 (.tip (.zero 7)) (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.tip (.cover 0 5 6))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.cover 0 4 5))) (.tip (.equal 2 6))) (.tip (.cover 0 5 6)))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.equal 3 5)))) (.tip (.equal 2 6))) (.tip (.cover 0 5 6))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 3 5))) (.tip (.cover 3 4 7))) (.tip (.cover 0 3 5))) (.tip (.cover 0 5 6)))))) (.split 13 (.tip (.zero 7)) (.tip (.cover 0 1 5)))) (.tip (.cover 0 1 4)))
private theorem q8Shape7T12OK : treeOK (forms 7) 1152 16664 q8Shape7T12=true := by decide

private def q8Shape7T10 : Tree := .split 10 q8Shape7T11 q8Shape7T12
private theorem q8Shape7T10OK : treeOK (forms 7) 128 16664 q8Shape7T10=true := by
  change (treeOK (forms 7) 128 (16664 ||| 2^10) q8Shape7T11 &&
    treeOK (forms 7) (128 ||| 2^10) 16664 q8Shape7T12)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T11OK,q8Shape7T12OK⟩

private def q8Shape7T13 : Tree := (.tip (.cover 0 1 3))
private theorem q8Shape7T13OK : treeOK (forms 7) 384 16408 q8Shape7T13=true := by decide

private def q8Shape7T9 : Tree := .split 8 q8Shape7T10 q8Shape7T13
private theorem q8Shape7T9OK : treeOK (forms 7) 128 16408 q8Shape7T9=true := by
  change (treeOK (forms 7) 128 (16408 ||| 2^8) q8Shape7T10 &&
    treeOK (forms 7) (128 ||| 2^8) 16408 q8Shape7T13)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T10OK,q8Shape7T13OK⟩

private def q8Shape7T3 : Tree := .split 7 q8Shape7T4 q8Shape7T9
private theorem q8Shape7T3OK : treeOK (forms 7) 0 16408 q8Shape7T3=true := by
  change (treeOK (forms 7) 0 (16408 ||| 2^7) q8Shape7T4 &&
    treeOK (forms 7) (0 ||| 2^7) 16408 q8Shape7T9)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T4OK,q8Shape7T9OK⟩

private def q8Shape7T17 : Tree := (.split 11 (.split 12 (.tip (.zero 6)) (.split 13 (.tip (.equal 6 7)) (.tip (.cover 0 1 5)))) (.split 12 (.tip (.zero 6)) (.split 13 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.split 5 (.split 6 (.tip (.small 1)) (.tip (.cover 0 4 5))) (.tip (.cover 0 4 5)))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.equal 3 7))) (.tip (.cover 0 4 5))) (.split 5 (.split 6 (.tip (.unordered 2 1)) (.tip (.equal 3 7))) (.tip (.cover 0 4 5))))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.cover 0 5 7))) (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 2 5))) (.tip (.cover 0 5 7)))) (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 2 5))) (.tip (.cover 0 4 5))) (.tip (.cover 2 4 6)))) (.tip (.cover 0 2 5)))) (.tip (.cover 0 1 5)))))
private theorem q8Shape7T17OK : treeOK (forms 7) 16 17800 q8Shape7T17=true := by decide

private def q8Shape7T18 : Tree := (.split 11 (.split 12 (.split 13 (.tip (.equal 6 7)) (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.split 5 (.split 6 (.tip (.small 1)) (.tip (.unordered 5 1))) (.tip (.cover 0 2 4)))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.cover 0 4 5))) (.tip (.cover 0 4 5))) (.split 5 (.split 6 (.tip (.unordered 2 1)) (.tip (.equal 3 7))) (.tip (.cover 0 2 4))))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.equal 2 4)))) (.tip (.cover 0 4 7))) (.tip (.cover 0 2 4))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 2 4))) (.tip (.cover 2 5 6))) (.tip (.cover 0 4 5))) (.tip (.cover 0 2 4)))))) (.split 13 (.split 0 (.split 1 (.split 2 (.split 5 (.tip (.small 1)) (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.unordered 4 1))))) (.split 5 (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.unordered 5 1)))) (.tip (.cover 0 2 4)))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.cover 0 2 5))) (.split 6 (.split 9 (.tip (.small 1)) (.tip (.unordered 4 1))) (.tip (.cover 4 5 7)))) (.split 5 (.split 6 (.tip (.equal 3 7)) (.tip (.cover 0 2 5))) (.tip (.cover 0 2 4))))) (.tip (.cover 0 2 6))) (.tip (.cover 0 1 5)))) (.tip (.cover 0 1 4)))
private theorem q8Shape7T18OK : treeOK (forms 7) 1040 16776 q8Shape7T18=true := by decide

private def q8Shape7T16 : Tree := .split 10 q8Shape7T17 q8Shape7T18
private theorem q8Shape7T16OK : treeOK (forms 7) 16 16776 q8Shape7T16=true := by
  change (treeOK (forms 7) 16 (16776 ||| 2^10) q8Shape7T17 &&
    treeOK (forms 7) (16 ||| 2^10) 16776 q8Shape7T18)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T17OK,q8Shape7T18OK⟩

private def q8Shape7T20 : Tree := (.split 11 (.split 12 (.tip (.zero 6)) (.split 13 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.split 5 (.split 6 (.tip (.small 1)) (.tip (.equal 2 3))) (.tip (.cover 0 3 5)))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.tip (.cover 2 3 6)))) (.split 5 (.split 6 (.tip (.equal 3 7)) (.tip (.cover 0 2 5))) (.tip (.cover 2 3 6))))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.unordered 3 1))) (.tip (.cover 0 3 5))) (.split 5 (.split 6 (.tip (.unordered 2 1)) (.tip (.unordered 2 1))) (.tip (.cover 0 3 5)))) (.tip (.cover 0 2 5)))) (.tip (.cover 0 1 5)))) (.split 12 (.tip (.zero 6)) (.tip (.cover 0 5 7))))
private theorem q8Shape7T20OK : treeOK (forms 7) 272 17544 q8Shape7T20=true := by decide

private def q8Shape7T21 : Tree := (.split 11 (.split 12 (.split 13 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.split 5 (.split 6 (.tip (.small 1)) (.tip (.equal 2 3))) (.tip (.cover 0 2 4)))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.tip (.cover 0 3 4)))) (.split 5 (.split 6 (.tip (.equal 3 7)) (.tip (.cover 2 3 6))) (.tip (.cover 0 2 4))))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.unordered 3 1))) (.split 6 (.tip (.unordered 3 1)) (.tip (.unordered 3 1)))) (.tip (.cover 0 2 4))) (.split 2 (.split 5 (.split 6 (.tip (.unordered 2 1)) (.tip (.equal 2 3))) (.split 6 (.tip (.unordered 2 1)) (.tip (.unordered 3 1)))) (.tip (.cover 0 2 4))))) (.tip (.cover 0 4 7))) (.tip (.cover 1 6 7))) (.tip (.cover 0 1 4)))
private theorem q8Shape7T21OK : treeOK (forms 7) 1296 16520 q8Shape7T21=true := by decide

private def q8Shape7T19 : Tree := .split 10 q8Shape7T20 q8Shape7T21
private theorem q8Shape7T19OK : treeOK (forms 7) 272 16520 q8Shape7T19=true := by
  change (treeOK (forms 7) 272 (16520 ||| 2^10) q8Shape7T20 &&
    treeOK (forms 7) (272 ||| 2^10) 16520 q8Shape7T21)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T20OK,q8Shape7T21OK⟩

private def q8Shape7T15 : Tree := .split 8 q8Shape7T16 q8Shape7T19
private theorem q8Shape7T15OK : treeOK (forms 7) 16 16520 q8Shape7T15=true := by
  change (treeOK (forms 7) 16 (16520 ||| 2^8) q8Shape7T16 &&
    treeOK (forms 7) (16 ||| 2^8) 16520 q8Shape7T19)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T16OK,q8Shape7T19OK⟩

private def q8Shape7T25 : Tree := (.split 12 (.split 13 (.tip (.equal 6 7)) (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.split 5 (.split 6 (.tip (.small 1)) (.tip (.unordered 5 1))) (.tip (.cover 0 2 3)))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.equal 2 3))) (.tip (.cover 0 3 7))) (.tip (.cover 0 2 3)))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.equal 3 5)))) (.tip (.cover 0 3 5))) (.split 5 (.split 6 (.tip (.unordered 2 1)) (.tip (.unordered 2 1))) (.tip (.cover 0 2 3)))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 3 5))) (.tip (.equal 2 3))) (.tip (.cover 0 3 5))) (.tip (.cover 0 2 3)))))) (.split 13 (.split 0 (.split 1 (.split 2 (.split 5 (.tip (.small 1)) (.split 6 (.tip (.small 1)) (.tip (.unordered 3 1)))) (.split 5 (.split 6 (.tip (.small 1)) (.tip (.unordered 5 1))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 2 6))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.unordered 3 1))) (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 2 5))) (.tip (.unordered 3 1)))) (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 2 5))) (.tip (.unordered 3 1))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 2 5)))) (.tip (.cover 0 1 5))))
private theorem q8Shape7T25OK : treeOK (forms 7) 144 19720 q8Shape7T25=true := by decide

private def q8Shape7T26 : Tree := (.split 12 (.split 13 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.split 5 (.split 6 (.tip (.small 1)) (.tip (.equal 2 3))) (.tip (.cover 0 2 3)))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.cover 0 2 3))) (.split 6 (.tip (.unordered 4 1)) (.tip (.cover 0 2 3)))) (.tip (.cover 0 2 3)))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.cover 0 3 4))) (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 3 4))) (.tip (.unordered 3 1)))) (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 3 4))) (.tip (.equal 2 3))) (.tip (.cover 0 2 3)))) (.split 2 (.split 5 (.split 6 (.tip (.unordered 2 1)) (.tip (.cover 0 2 3))) (.split 6 (.tip (.unordered 2 1)) (.tip (.unordered 3 1)))) (.tip (.cover 0 2 3))))) (.tip (.cover 0 3 7))) (.tip (.cover 1 6 7)))
private theorem q8Shape7T26OK : treeOK (forms 7) 2192 17672 q8Shape7T26=true := by decide

private def q8Shape7T24 : Tree := .split 11 q8Shape7T25 q8Shape7T26
private theorem q8Shape7T24OK : treeOK (forms 7) 144 17672 q8Shape7T24=true := by
  change (treeOK (forms 7) 144 (17672 ||| 2^11) q8Shape7T25 &&
    treeOK (forms 7) (144 ||| 2^11) 17672 q8Shape7T26)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T25OK,q8Shape7T26OK⟩

private def q8Shape7T27 : Tree := (.split 11 (.split 12 (.split 13 (.split 0 (.split 1 (.split 2 (.split 5 (.tip (.small 1)) (.split 6 (.tip (.small 1)) (.tip (.unordered 3 1)))) (.tip (.cover 0 2 6))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.equal 2 3))) (.split 6 (.tip (.unordered 4 1)) (.tip (.cover 0 2 3)))) (.tip (.cover 0 2 3)))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.equal 2 4)))) (.split 6 (.tip (.unordered 3 1)) (.tip (.unordered 3 1)))) (.tip (.cover 0 2 4))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 2 4))) (.tip (.equal 2 3))) (.split 6 (.tip (.unordered 3 1)) (.tip (.unordered 3 1)))) (.tip (.cover 0 2 3))))) (.tip (.cover 1 6 7))) (.tip (.cover 0 2 6))) (.tip (.cover 0 1 4)))
private theorem q8Shape7T27OK : treeOK (forms 7) 1168 16648 q8Shape7T27=true := by decide

private def q8Shape7T23 : Tree := .split 10 q8Shape7T24 q8Shape7T27
private theorem q8Shape7T23OK : treeOK (forms 7) 144 16648 q8Shape7T23=true := by
  change (treeOK (forms 7) 144 (16648 ||| 2^10) q8Shape7T24 &&
    treeOK (forms 7) (144 ||| 2^10) 16648 q8Shape7T27)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T24OK,q8Shape7T27OK⟩

private def q8Shape7T28 : Tree := (.tip (.cover 0 1 3))
private theorem q8Shape7T28OK : treeOK (forms 7) 400 16392 q8Shape7T28=true := by decide

private def q8Shape7T22 : Tree := .split 8 q8Shape7T23 q8Shape7T28
private theorem q8Shape7T22OK : treeOK (forms 7) 144 16392 q8Shape7T22=true := by
  change (treeOK (forms 7) 144 (16392 ||| 2^8) q8Shape7T23 &&
    treeOK (forms 7) (144 ||| 2^8) 16392 q8Shape7T28)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T23OK,q8Shape7T28OK⟩

private def q8Shape7T14 : Tree := .split 7 q8Shape7T15 q8Shape7T22
private theorem q8Shape7T14OK : treeOK (forms 7) 16 16392 q8Shape7T14=true := by
  change (treeOK (forms 7) 16 (16392 ||| 2^7) q8Shape7T15 &&
    treeOK (forms 7) (16 ||| 2^7) 16392 q8Shape7T22)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T15OK,q8Shape7T22OK⟩

private def q8Shape7T2 : Tree := .split 4 q8Shape7T3 q8Shape7T14
private theorem q8Shape7T2OK : treeOK (forms 7) 0 16392 q8Shape7T2=true := by
  change (treeOK (forms 7) 0 (16392 ||| 2^4) q8Shape7T3 &&
    treeOK (forms 7) (0 ||| 2^4) 16392 q8Shape7T14)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T3OK,q8Shape7T14OK⟩

private def q8Shape7T34 : Tree := (.split 12 (.split 13 (.tip (.zero 7)) (.tip (.equal 6 7))) (.split 13 (.tip (.zero 7)) (.tip (.cover 0 1 5))))
private theorem q8Shape7T34OK : treeOK (forms 7) 8 19856 q8Shape7T34=true := by decide

private def q8Shape7T35 : Tree := (.split 12 (.split 13 (.tip (.equal 6 7)) (.split 0 (.split 1 (.split 2 (.split 5 (.tip (.small 1)) (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.unordered 4 1))))) (.split 5 (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.unordered 5 1)))) (.tip (.cover 0 2 4)))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.cover 0 2 5))) (.split 6 (.split 9 (.tip (.small 1)) (.tip (.unordered 4 1))) (.tip (.cover 4 5 6)))) (.split 5 (.split 6 (.tip (.equal 3 6)) (.tip (.cover 0 2 5))) (.tip (.cover 0 2 4))))) (.tip (.cover 0 2 7)))) (.split 13 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.split 5 (.split 6 (.tip (.small 1)) (.tip (.unordered 5 1))) (.tip (.cover 0 2 4)))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.cover 0 4 5))) (.tip (.cover 0 4 5))) (.split 5 (.split 6 (.tip (.unordered 2 1)) (.tip (.equal 3 6))) (.tip (.cover 0 2 4))))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.equal 2 4)))) (.tip (.cover 0 4 6))) (.tip (.cover 0 2 4))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 2 4))) (.tip (.cover 2 5 7))) (.tip (.cover 0 4 5))) (.tip (.cover 0 2 4))))) (.tip (.cover 0 1 5))))
private theorem q8Shape7T35OK : treeOK (forms 7) 2056 17808 q8Shape7T35=true := by decide

private def q8Shape7T33 : Tree := .split 11 q8Shape7T34 q8Shape7T35
private theorem q8Shape7T33OK : treeOK (forms 7) 8 17808 q8Shape7T33=true := by
  change (treeOK (forms 7) 8 (17808 ||| 2^11) q8Shape7T34 &&
    treeOK (forms 7) (8 ||| 2^11) 17808 q8Shape7T35)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T34OK,q8Shape7T35OK⟩

private def q8Shape7T36 : Tree := (.split 11 (.split 12 (.split 13 (.tip (.zero 7)) (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.split 5 (.split 6 (.tip (.small 1)) (.tip (.cover 0 4 5))) (.tip (.cover 0 4 5)))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.equal 3 6))) (.tip (.cover 0 4 5))) (.split 5 (.split 6 (.tip (.unordered 2 1)) (.tip (.equal 3 6))) (.tip (.cover 0 4 5))))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.cover 0 5 6))) (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 2 5))) (.tip (.cover 0 5 6)))) (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 2 5))) (.tip (.cover 0 4 5))) (.tip (.cover 2 4 7)))) (.tip (.cover 0 2 5))))) (.split 13 (.tip (.zero 7)) (.tip (.cover 0 1 5)))) (.tip (.cover 0 1 4)))
private theorem q8Shape7T36OK : treeOK (forms 7) 1032 16784 q8Shape7T36=true := by decide

private def q8Shape7T32 : Tree := .split 10 q8Shape7T33 q8Shape7T36
private theorem q8Shape7T32OK : treeOK (forms 7) 8 16784 q8Shape7T32=true := by
  change (treeOK (forms 7) 8 (16784 ||| 2^10) q8Shape7T33 &&
    treeOK (forms 7) (8 ||| 2^10) 16784 q8Shape7T36)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T33OK,q8Shape7T36OK⟩

private def q8Shape7T39 : Tree := (.split 12 (.split 13 (.tip (.equal 6 7)) (.split 0 (.split 1 (.split 2 (.split 5 (.tip (.small 1)) (.split 6 (.tip (.small 1)) (.tip (.unordered 3 1)))) (.split 5 (.split 6 (.tip (.small 1)) (.tip (.unordered 5 1))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 2 7))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.unordered 3 1))) (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 2 5))) (.tip (.unordered 3 1)))) (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 2 5))) (.tip (.unordered 3 1))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 2 5))))) (.split 13 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.split 5 (.split 6 (.tip (.small 1)) (.tip (.unordered 5 1))) (.tip (.cover 0 2 3)))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.equal 2 3))) (.tip (.cover 0 3 6))) (.tip (.cover 0 2 3)))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.equal 3 5)))) (.tip (.cover 0 3 5))) (.split 5 (.split 6 (.tip (.unordered 2 1)) (.tip (.unordered 2 1))) (.tip (.cover 0 2 3)))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 3 5))) (.tip (.equal 2 3))) (.tip (.cover 0 3 5))) (.tip (.cover 0 2 3))))) (.tip (.cover 0 1 5))))
private theorem q8Shape7T39OK : treeOK (forms 7) 264 19600 q8Shape7T39=true := by decide

private def q8Shape7T40 : Tree := (.split 12 (.split 13 (.split 0 (.split 1 (.split 2 (.split 5 (.tip (.small 1)) (.split 6 (.tip (.small 1)) (.tip (.unordered 3 1)))) (.tip (.cover 0 2 7))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.equal 2 3))) (.split 6 (.tip (.unordered 4 1)) (.tip (.cover 0 2 3)))) (.tip (.cover 0 2 3)))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.equal 2 4)))) (.split 6 (.tip (.unordered 3 1)) (.tip (.unordered 3 1)))) (.tip (.cover 0 2 4))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 2 4))) (.tip (.equal 2 3))) (.split 6 (.tip (.unordered 3 1)) (.tip (.unordered 3 1)))) (.tip (.cover 0 2 3))))) (.tip (.cover 0 2 7))) (.tip (.cover 1 6 7)))
private theorem q8Shape7T40OK : treeOK (forms 7) 2312 17552 q8Shape7T40=true := by decide

private def q8Shape7T38 : Tree := .split 11 q8Shape7T39 q8Shape7T40
private theorem q8Shape7T38OK : treeOK (forms 7) 264 17552 q8Shape7T38=true := by
  change (treeOK (forms 7) 264 (17552 ||| 2^11) q8Shape7T39 &&
    treeOK (forms 7) (264 ||| 2^11) 17552 q8Shape7T40)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T39OK,q8Shape7T40OK⟩

private def q8Shape7T41 : Tree := (.split 11 (.split 12 (.split 13 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.split 5 (.split 6 (.tip (.small 1)) (.tip (.equal 2 3))) (.tip (.cover 0 2 3)))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.cover 0 2 3))) (.split 6 (.tip (.unordered 4 1)) (.tip (.cover 0 2 3)))) (.tip (.cover 0 2 3)))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.cover 0 3 4))) (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 3 4))) (.tip (.unordered 3 1)))) (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 3 4))) (.tip (.equal 2 3))) (.tip (.cover 0 2 3)))) (.split 2 (.split 5 (.split 6 (.tip (.unordered 2 1)) (.tip (.cover 0 2 3))) (.split 6 (.tip (.unordered 2 1)) (.tip (.unordered 3 1)))) (.tip (.cover 0 2 3))))) (.tip (.cover 1 6 7))) (.tip (.cover 0 3 6))) (.tip (.cover 0 1 4)))
private theorem q8Shape7T41OK : treeOK (forms 7) 1288 16528 q8Shape7T41=true := by decide

private def q8Shape7T37 : Tree := .split 10 q8Shape7T38 q8Shape7T41
private theorem q8Shape7T37OK : treeOK (forms 7) 264 16528 q8Shape7T37=true := by
  change (treeOK (forms 7) 264 (16528 ||| 2^10) q8Shape7T38 &&
    treeOK (forms 7) (264 ||| 2^10) 16528 q8Shape7T41)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T38OK,q8Shape7T41OK⟩

private def q8Shape7T31 : Tree := .split 8 q8Shape7T32 q8Shape7T37
private theorem q8Shape7T31OK : treeOK (forms 7) 8 16528 q8Shape7T31=true := by
  change (treeOK (forms 7) 8 (16528 ||| 2^8) q8Shape7T32 &&
    treeOK (forms 7) (8 ||| 2^8) 16528 q8Shape7T37)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T32OK,q8Shape7T37OK⟩

private def q8Shape7T45 : Tree := (.split 12 (.split 13 (.tip (.zero 7)) (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.split 5 (.split 6 (.tip (.small 1)) (.tip (.equal 2 3))) (.tip (.cover 0 3 5)))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.tip (.cover 2 3 7)))) (.split 5 (.split 6 (.tip (.equal 3 6)) (.tip (.cover 0 2 5))) (.tip (.cover 2 3 7))))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.unordered 3 1))) (.tip (.cover 0 3 5))) (.split 5 (.split 6 (.tip (.unordered 2 1)) (.tip (.unordered 2 1))) (.tip (.cover 0 3 5)))) (.tip (.cover 0 2 5))))) (.split 13 (.tip (.zero 7)) (.tip (.cover 0 1 5))))
private theorem q8Shape7T45OK : treeOK (forms 7) 136 19728 q8Shape7T45=true := by decide

private def q8Shape7T46 : Tree := (.split 12 (.split 13 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.split 5 (.split 6 (.tip (.small 1)) (.tip (.equal 2 3))) (.tip (.cover 0 2 4)))) (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.tip (.cover 0 3 4)))) (.split 5 (.split 6 (.tip (.equal 3 6)) (.tip (.cover 2 3 7))) (.tip (.cover 0 2 4))))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.tip (.unordered 3 1))) (.split 6 (.tip (.unordered 3 1)) (.tip (.unordered 3 1)))) (.tip (.cover 0 2 4))) (.split 2 (.split 5 (.split 6 (.tip (.unordered 2 1)) (.tip (.equal 2 3))) (.split 6 (.tip (.unordered 2 1)) (.tip (.unordered 3 1)))) (.tip (.cover 0 2 4))))) (.tip (.cover 1 6 7))) (.tip (.cover 0 4 6)))
private theorem q8Shape7T46OK : treeOK (forms 7) 2184 17680 q8Shape7T46=true := by decide

private def q8Shape7T44 : Tree := .split 11 q8Shape7T45 q8Shape7T46
private theorem q8Shape7T44OK : treeOK (forms 7) 136 17680 q8Shape7T44=true := by
  change (treeOK (forms 7) 136 (17680 ||| 2^11) q8Shape7T45 &&
    treeOK (forms 7) (136 ||| 2^11) 17680 q8Shape7T46)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T45OK,q8Shape7T46OK⟩

private def q8Shape7T47 : Tree := (.split 11 (.split 12 (.split 13 (.tip (.zero 7)) (.tip (.cover 0 5 6))) (.tip (.cover 1 6 7))) (.tip (.cover 0 1 4)))
private theorem q8Shape7T47OK : treeOK (forms 7) 1160 16656 q8Shape7T47=true := by decide

private def q8Shape7T43 : Tree := .split 10 q8Shape7T44 q8Shape7T47
private theorem q8Shape7T43OK : treeOK (forms 7) 136 16656 q8Shape7T43=true := by
  change (treeOK (forms 7) 136 (16656 ||| 2^10) q8Shape7T44 &&
    treeOK (forms 7) (136 ||| 2^10) 16656 q8Shape7T47)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T44OK,q8Shape7T47OK⟩

private def q8Shape7T48 : Tree := (.tip (.cover 0 1 3))
private theorem q8Shape7T48OK : treeOK (forms 7) 392 16400 q8Shape7T48=true := by decide

private def q8Shape7T42 : Tree := .split 8 q8Shape7T43 q8Shape7T48
private theorem q8Shape7T42OK : treeOK (forms 7) 136 16400 q8Shape7T42=true := by
  change (treeOK (forms 7) 136 (16400 ||| 2^8) q8Shape7T43 &&
    treeOK (forms 7) (136 ||| 2^8) 16400 q8Shape7T48)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T43OK,q8Shape7T48OK⟩

private def q8Shape7T30 : Tree := .split 7 q8Shape7T31 q8Shape7T42
private theorem q8Shape7T30OK : treeOK (forms 7) 8 16400 q8Shape7T30=true := by
  change (treeOK (forms 7) 8 (16400 ||| 2^7) q8Shape7T31 &&
    treeOK (forms 7) (8 ||| 2^7) 16400 q8Shape7T42)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T31OK,q8Shape7T42OK⟩

private def q8Shape7T49 : Tree := (.tip (.cover 0 1 2))
private theorem q8Shape7T49OK : treeOK (forms 7) 24 16384 q8Shape7T49=true := by decide

private def q8Shape7T29 : Tree := .split 4 q8Shape7T30 q8Shape7T49
private theorem q8Shape7T29OK : treeOK (forms 7) 8 16384 q8Shape7T29=true := by
  change (treeOK (forms 7) 8 (16384 ||| 2^4) q8Shape7T30 &&
    treeOK (forms 7) (8 ||| 2^4) 16384 q8Shape7T49)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T30OK,q8Shape7T49OK⟩

private def q8Shape7T1 : Tree := .split 3 q8Shape7T2 q8Shape7T29
private theorem q8Shape7T1OK : treeOK (forms 7) 0 16384 q8Shape7T1=true := by
  change (treeOK (forms 7) 0 (16384 ||| 2^3) q8Shape7T2 &&
    treeOK (forms 7) (0 ||| 2^3) 16384 q8Shape7T29)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T2OK,q8Shape7T29OK⟩

private def q8Shape7T50 : Tree := (.tip (.cover 0 1 6))
private theorem q8Shape7T50OK : treeOK (forms 7) 16384 0 q8Shape7T50=true := by decide

private def q8Shape7T0 : Tree := .split 14 q8Shape7T1 q8Shape7T50
private theorem q8Shape7T0OK : treeOK (forms 7) 0 0 q8Shape7T0=true := by
  change (treeOK (forms 7) 0 (0 ||| 2^14) q8Shape7T1 &&
    treeOK (forms 7) (0 ||| 2^14) 0 q8Shape7T50)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape7T1OK,q8Shape7T50OK⟩


theorem q8Shape7_cover (b : Nat→Bool) (H : Ranked (adj (forms 7) b)) :
    ∃ u v w,Dominates3 (adj (forms 7) b) u v w :=
  checked_tree (forms 7) b H q8Shape7T0 q8Shape7T0OK

#print axioms q8Shape7_cover
end Graffiti384b.Q8
