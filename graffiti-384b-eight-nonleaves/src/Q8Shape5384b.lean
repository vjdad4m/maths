import Q8MaskKernel384b

namespace Graffiti384b.Q8
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
private def q8Shape5T3 : Tree := (.split 5 (.tip (.small 1)) (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.split 3 (.split 7 (.split 10 (.split 12 (.tip (.equal 0 1)) (.tip (.unordered 5 1))) (.tip (.unordered 4 1))) (.tip (.unordered 3 1))) (.split 7 (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 3 4)) (.split 13 (.tip (.equal 3 4)) (.tip (.unordered 4 1)))) (.split 11 (.split 13 (.tip (.equal 3 4)) (.tip (.unordered 3 1))) (.tip (.unordered 3 1)))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.cover 0 2 4))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 1 7))) (.tip (.unordered 5 1))) (.tip (.unordered 4 1))) (.tip (.unordered 3 1)))))))
private theorem q8Shape5T3OK : treeOK (forms 5) 0 7 q8Shape5T3=true := by decide

private def q8Shape5T5 : Tree := (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.unordered 5 1))))
private theorem q8Shape5T5OK : treeOK (forms 5) 4 35 q8Shape5T5=true := by decide

private def q8Shape5T8 : Tree := (.tip (.small 1))
private theorem q8Shape5T8OK : treeOK (forms 5) 36 579 q8Shape5T8=true := by decide

private def q8Shape5T10 : Tree := (.split 7 (.split 10 (.split 12 (.tip (.equal 0 1)) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.tip (.cover 0 5 7))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.unordered 5 1))) (.split 13 (.tip (.equal 2 3)) (.tip (.unordered 5 0)))) (.tip (.cover 0 5 7)))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.tip (.equal 2 3)) (.tip (.unordered 4 1)))) (.tip (.cover 0 4 7))) (.tip (.cover 0 1 7))) (.tip (.unordered 4 1)))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 4 5)) (.split 13 (.tip (.equal 4 5)) (.tip (.equal 4 5)))) (.split 11 (.tip (.equal 4 5)) (.split 13 (.tip (.equal 3 5)) (.tip (.unordered 4 1))))) (.split 8 (.split 11 (.split 13 (.tip (.equal 4 5)) (.tip (.equal 2 3))) (.tip (.cover 2 4 6))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.zero 7)) (.split 13 (.tip (.zero 7)) (.tip (.unordered 5 1)))) (.tip (.cover 0 5 7))) (.tip (.cover 3 5 7))) (.tip (.cover 0 1 7)))) (.tip (.unordered 4 1))))
private theorem q8Shape5T10OK : treeOK (forms 5) 548 75 q8Shape5T10=true := by decide

private def q8Shape5T11 : Tree := (.split 7 (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 4 5)) (.split 13 (.tip (.equal 4 5)) (.tip (.equal 4 5)))) (.split 11 (.tip (.equal 4 5)) (.tip (.equal 2 3)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 4 5)) (.tip (.equal 2 4))) (.tip (.cover 0 2 4))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 1 7))) (.tip (.unordered 5 1))) (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.zero 7)) (.split 13 (.tip (.zero 7)) (.tip (.unordered 4 1)))) (.tip (.cover 2 4 7))) (.tip (.cover 0 4 7))) (.tip (.cover 0 1 7))) (.tip (.unordered 4 1)))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.tip (.equal 2 3)) (.tip (.cover 2 3 4)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.equal 2 4))) (.tip (.cover 2 3 4))) (.tip (.cover 2 3 4)))) (.tip (.cover 0 1 7))) (.tip (.unordered 5 1))) (.tip (.unordered 4 1))))
private theorem q8Shape5T11OK : treeOK (forms 5) 556 67 q8Shape5T11=true := by decide

private def q8Shape5T9 : Tree := .split 3 q8Shape5T10 q8Shape5T11
private theorem q8Shape5T9OK : treeOK (forms 5) 548 67 q8Shape5T9=true := by
  change (treeOK (forms 5) 548 (67 ||| 2^3) q8Shape5T10 &&
    treeOK (forms 5) (548 ||| 2^3) 67 q8Shape5T11)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T10OK,q8Shape5T11OK⟩

private def q8Shape5T7 : Tree := .split 9 q8Shape5T8 q8Shape5T9
private theorem q8Shape5T7OK : treeOK (forms 5) 36 67 q8Shape5T7=true := by
  change (treeOK (forms 5) 36 (67 ||| 2^9) q8Shape5T8 &&
    treeOK (forms 5) (36 ||| 2^9) 67 q8Shape5T9)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T8OK,q8Shape5T9OK⟩

private def q8Shape5T14 : Tree := (.split 7 (.split 10 (.split 12 (.tip (.equal 0 1)) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 4)) (.split 11 (.tip (.equal 2 4)) (.tip (.cover 0 5 7)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 4)) (.tip (.unordered 5 1))) (.tip (.cover 0 5 7))) (.split 11 (.split 13 (.tip (.equal 2 4)) (.tip (.unordered 5 0))) (.tip (.cover 0 5 7))))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 3 5)) (.split 11 (.split 13 (.tip (.equal 3 5)) (.tip (.equal 3 5))) (.split 13 (.tip (.equal 4 5)) (.tip (.unordered 3 1))))) (.split 8 (.split 11 (.split 13 (.tip (.equal 3 5)) (.tip (.equal 2 4))) (.tip (.cover 0 2 4))) (.tip (.cover 2 3 6)))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.tip (.zero 7)) (.split 11 (.split 13 (.tip (.zero 7)) (.tip (.unordered 5 1))) (.tip (.cover 0 5 7)))) (.tip (.cover 4 5 7))) (.tip (.cover 0 1 7))))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 4)) (.split 11 (.tip (.equal 2 4)) (.tip (.unordered 3 1)))) (.tip (.cover 0 3 7))) (.tip (.cover 0 1 7))) (.tip (.unordered 3 1))) (.tip (.unordered 3 1))))
private theorem q8Shape5T14OK : treeOK (forms 5) 100 523 q8Shape5T14=true := by decide

private def q8Shape5T15 : Tree := (.split 7 (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 3 5)) (.split 11 (.split 13 (.tip (.equal 3 5)) (.tip (.equal 3 5))) (.tip (.equal 2 4)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 3 5)) (.tip (.equal 2 3))) (.tip (.cover 0 2 4))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 1 7))) (.tip (.unordered 5 1))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 4)) (.split 11 (.tip (.equal 2 4)) (.tip (.cover 2 3 4)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 4)) (.tip (.equal 2 3))) (.tip (.cover 2 3 4))) (.tip (.cover 2 3 4)))) (.tip (.cover 0 1 7))) (.tip (.unordered 5 1)))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.zero 7)) (.split 11 (.split 13 (.tip (.zero 7)) (.tip (.unordered 3 1))) (.tip (.unordered 3 1)))) (.tip (.cover 0 3 7))) (.tip (.cover 0 1 7))) (.tip (.unordered 3 1))) (.tip (.unordered 3 1))))
private theorem q8Shape5T15OK : treeOK (forms 5) 108 515 q8Shape5T15=true := by decide

private def q8Shape5T13 : Tree := .split 3 q8Shape5T14 q8Shape5T15
private theorem q8Shape5T13OK : treeOK (forms 5) 100 515 q8Shape5T13=true := by
  change (treeOK (forms 5) 100 (515 ||| 2^3) q8Shape5T14 &&
    treeOK (forms 5) (100 ||| 2^3) 515 q8Shape5T15)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T14OK,q8Shape5T15OK⟩

private def q8Shape5T16 : Tree := (.tip (.unordered 5 1))
private theorem q8Shape5T16OK : treeOK (forms 5) 612 3 q8Shape5T16=true := by decide

private def q8Shape5T12 : Tree := .split 9 q8Shape5T13 q8Shape5T16
private theorem q8Shape5T12OK : treeOK (forms 5) 100 3 q8Shape5T12=true := by
  change (treeOK (forms 5) 100 (3 ||| 2^9) q8Shape5T13 &&
    treeOK (forms 5) (100 ||| 2^9) 3 q8Shape5T16)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T13OK,q8Shape5T16OK⟩

private def q8Shape5T6 : Tree := .split 6 q8Shape5T7 q8Shape5T12
private theorem q8Shape5T6OK : treeOK (forms 5) 36 3 q8Shape5T6=true := by
  change (treeOK (forms 5) 36 (3 ||| 2^6) q8Shape5T7 &&
    treeOK (forms 5) (36 ||| 2^6) 3 q8Shape5T12)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T7OK,q8Shape5T12OK⟩

private def q8Shape5T4 : Tree := .split 5 q8Shape5T5 q8Shape5T6
private theorem q8Shape5T4OK : treeOK (forms 5) 4 3 q8Shape5T4=true := by
  change (treeOK (forms 5) 4 (3 ||| 2^5) q8Shape5T5 &&
    treeOK (forms 5) (4 ||| 2^5) 3 q8Shape5T6)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T5OK,q8Shape5T6OK⟩

private def q8Shape5T2 : Tree := .split 2 q8Shape5T3 q8Shape5T4
private theorem q8Shape5T2OK : treeOK (forms 5) 0 3 q8Shape5T2=true := by
  change (treeOK (forms 5) 0 (3 ||| 2^2) q8Shape5T3 &&
    treeOK (forms 5) (0 ||| 2^2) 3 q8Shape5T4)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T3OK,q8Shape5T4OK⟩

private def q8Shape5T20 : Tree := (.tip (.small 1))
private theorem q8Shape5T20OK : treeOK (forms 5) 2 101 q8Shape5T20=true := by decide

private def q8Shape5T22 : Tree := (.tip (.small 1))
private theorem q8Shape5T22OK : treeOK (forms 5) 66 549 q8Shape5T22=true := by decide

private def q8Shape5T24 : Tree := (.split 7 (.split 10 (.split 12 (.tip (.equal 0 1)) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.unordered 5 1))) (.split 13 (.tip (.equal 2 3)) (.tip (.unordered 5 0))))) (.tip (.cover 0 5 7))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.tip (.cover 0 4 7))) (.split 8 (.split 11 (.tip (.equal 2 3)) (.tip (.unordered 4 1))) (.tip (.cover 0 4 7)))) (.tip (.cover 0 1 7))) (.tip (.unordered 4 1)))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 4 5)) (.split 13 (.tip (.equal 4 5)) (.tip (.equal 4 5)))) (.split 11 (.split 13 (.tip (.equal 4 5)) (.tip (.equal 3 4))) (.tip (.cover 0 3 4)))) (.split 8 (.split 11 (.tip (.equal 4 5)) (.tip (.equal 2 3))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 1 7))) (.tip (.unordered 5 1))) (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.zero 7)) (.split 13 (.tip (.zero 7)) (.tip (.unordered 4 1)))) (.tip (.cover 0 4 7))) (.tip (.cover 3 4 7))) (.tip (.cover 0 1 7))) (.tip (.unordered 4 1)))))
private theorem q8Shape5T24OK : treeOK (forms 5) 578 45 q8Shape5T24=true := by decide

private def q8Shape5T25 : Tree := (.split 7 (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 4 5)) (.split 13 (.tip (.equal 4 5)) (.tip (.equal 4 5)))) (.split 11 (.split 13 (.tip (.equal 4 5)) (.tip (.equal 2 3))) (.tip (.cover 3 4 6)))) (.split 8 (.split 11 (.tip (.equal 4 5)) (.split 13 (.tip (.equal 2 5)) (.tip (.unordered 4 1)))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.zero 7)) (.split 13 (.tip (.zero 7)) (.tip (.unordered 5 1)))) (.tip (.cover 2 5 7))) (.tip (.cover 0 5 7))) (.tip (.cover 0 1 7)))) (.tip (.unordered 4 1))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.equal 3 4))) (.tip (.cover 2 3 4)))) (.split 8 (.split 11 (.tip (.equal 2 3)) (.tip (.cover 2 3 4))) (.tip (.cover 2 3 4)))) (.tip (.cover 0 1 7))) (.tip (.unordered 5 1))) (.tip (.unordered 4 1))))
private theorem q8Shape5T25OK : treeOK (forms 5) 586 37 q8Shape5T25=true := by decide

private def q8Shape5T23 : Tree := .split 3 q8Shape5T24 q8Shape5T25
private theorem q8Shape5T23OK : treeOK (forms 5) 578 37 q8Shape5T23=true := by
  change (treeOK (forms 5) 578 (37 ||| 2^3) q8Shape5T24 &&
    treeOK (forms 5) (578 ||| 2^3) 37 q8Shape5T25)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T24OK,q8Shape5T25OK⟩

private def q8Shape5T21 : Tree := .split 9 q8Shape5T22 q8Shape5T23
private theorem q8Shape5T21OK : treeOK (forms 5) 66 37 q8Shape5T21=true := by
  change (treeOK (forms 5) 66 (37 ||| 2^9) q8Shape5T22 &&
    treeOK (forms 5) (66 ||| 2^9) 37 q8Shape5T23)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T22OK,q8Shape5T23OK⟩

private def q8Shape5T19 : Tree := .split 6 q8Shape5T20 q8Shape5T21
private theorem q8Shape5T19OK : treeOK (forms 5) 2 37 q8Shape5T19=true := by
  change (treeOK (forms 5) 2 (37 ||| 2^6) q8Shape5T20 &&
    treeOK (forms 5) (2 ||| 2^6) 37 q8Shape5T21)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T20OK,q8Shape5T21OK⟩

private def q8Shape5T27 : Tree := (.split 9 (.tip (.small 1)) (.tip (.unordered 4 1)))
private theorem q8Shape5T27OK : treeOK (forms 5) 34 69 q8Shape5T27=true := by decide

private def q8Shape5T30 : Tree := (.split 7 (.split 10 (.split 12 (.tip (.equal 0 1)) (.split 14 (.split 4 (.split 8 (.tip (.equal 3 4)) (.split 11 (.split 13 (.tip (.equal 3 4)) (.tip (.equal 4 5))) (.split 13 (.tip (.equal 3 4)) (.tip (.unordered 3 1))))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.equal 2 5))) (.tip (.cover 2 3 6)))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 5)) (.split 11 (.split 13 (.tip (.equal 2 5)) (.tip (.equal 3 4))) (.tip (.unordered 4 1)))) (.split 8 (.split 11 (.tip (.equal 2 5)) (.tip (.unordered 4 1))) (.split 11 (.split 13 (.tip (.equal 2 5)) (.tip (.equal 3 4))) (.tip (.unordered 4 0))))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.tip (.zero 7)) (.split 11 (.split 13 (.tip (.zero 7)) (.tip (.equal 3 4))) (.tip (.unordered 4 1)))) (.tip (.cover 4 5 7))) (.tip (.cover 0 1 7))))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 5)) (.split 11 (.split 13 (.tip (.equal 2 5)) (.tip (.unordered 3 1))) (.tip (.unordered 3 1)))) (.tip (.cover 0 3 7))) (.tip (.cover 0 1 7))) (.tip (.unordered 3 1))) (.tip (.unordered 3 1))))
private theorem q8Shape5T30OK : treeOK (forms 5) 98 525 q8Shape5T30=true := by decide

private def q8Shape5T31 : Tree := (.split 7 (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 3 4)) (.split 11 (.split 13 (.tip (.equal 3 4)) (.tip (.equal 2 5))) (.split 13 (.tip (.equal 3 4)) (.tip (.unordered 3 1))))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.equal 2 3))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 5)) (.split 11 (.split 13 (.tip (.equal 2 5)) (.tip (.equal 4 5))) (.tip (.cover 2 5 7)))) (.split 8 (.split 11 (.tip (.equal 2 5)) (.tip (.equal 2 3))) (.tip (.cover 2 3 5)))) (.tip (.cover 0 1 7)))) (.tip (.unordered 4 1))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.zero 7)) (.split 11 (.split 13 (.tip (.zero 7)) (.tip (.unordered 3 1))) (.tip (.unordered 3 1)))) (.tip (.cover 0 3 7))) (.tip (.cover 0 1 7))) (.tip (.unordered 3 1))) (.tip (.unordered 3 1))))
private theorem q8Shape5T31OK : treeOK (forms 5) 106 517 q8Shape5T31=true := by decide

private def q8Shape5T29 : Tree := .split 3 q8Shape5T30 q8Shape5T31
private theorem q8Shape5T29OK : treeOK (forms 5) 98 517 q8Shape5T29=true := by
  change (treeOK (forms 5) 98 (517 ||| 2^3) q8Shape5T30 &&
    treeOK (forms 5) (98 ||| 2^3) 517 q8Shape5T31)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T30OK,q8Shape5T31OK⟩

private def q8Shape5T32 : Tree := (.tip (.unordered 4 1))
private theorem q8Shape5T32OK : treeOK (forms 5) 610 5 q8Shape5T32=true := by decide

private def q8Shape5T28 : Tree := .split 9 q8Shape5T29 q8Shape5T32
private theorem q8Shape5T28OK : treeOK (forms 5) 98 5 q8Shape5T28=true := by
  change (treeOK (forms 5) 98 (5 ||| 2^9) q8Shape5T29 &&
    treeOK (forms 5) (98 ||| 2^9) 5 q8Shape5T32)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T29OK,q8Shape5T32OK⟩

private def q8Shape5T26 : Tree := .split 6 q8Shape5T27 q8Shape5T28
private theorem q8Shape5T26OK : treeOK (forms 5) 34 5 q8Shape5T26=true := by
  change (treeOK (forms 5) 34 (5 ||| 2^6) q8Shape5T27 &&
    treeOK (forms 5) (34 ||| 2^6) 5 q8Shape5T28)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T27OK,q8Shape5T28OK⟩

private def q8Shape5T18 : Tree := .split 5 q8Shape5T19 q8Shape5T26
private theorem q8Shape5T18OK : treeOK (forms 5) 2 5 q8Shape5T18=true := by
  change (treeOK (forms 5) 2 (5 ||| 2^5) q8Shape5T19 &&
    treeOK (forms 5) (2 ||| 2^5) 5 q8Shape5T26)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T19OK,q8Shape5T26OK⟩

private def q8Shape5T35 : Tree := (.split 9 (.tip (.small 1)) (.split 3 (.split 7 (.split 10 (.split 12 (.tip (.equal 0 1)) (.tip (.unordered 5 1))) (.tip (.unordered 4 1))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 4)) (.split 13 (.tip (.equal 2 4)) (.tip (.unordered 4 1)))) (.split 11 (.tip (.equal 2 4)) (.tip (.cover 0 3 4)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 4)) (.tip (.unordered 2 1))) (.tip (.unordered 2 1))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 1 7))) (.tip (.unordered 5 1))) (.tip (.unordered 4 1)))) (.tip (.unordered 2 1))))
private theorem q8Shape5T35OK : treeOK (forms 5) 6 97 q8Shape5T35=true := by decide

private def q8Shape5T39 : Tree := (.split 10 (.split 12 (.tip (.equal 0 1)) (.split 14 (.split 4 (.split 8 (.tip (.equal 3 4)) (.split 11 (.split 13 (.tip (.equal 3 4)) (.tip (.unordered 5 1))) (.tip (.cover 0 5 7)))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.cover 0 5 7))) (.split 11 (.split 13 (.tip (.equal 3 4)) (.tip (.unordered 5 0))) (.tip (.cover 0 5 7))))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 5)) (.split 11 (.split 13 (.tip (.equal 2 5)) (.tip (.equal 3 4))) (.tip (.cover 0 3 4)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 5)) (.tip (.equal 2 5))) (.split 13 (.tip (.equal 4 5)) (.tip (.unordered 2 1)))) (.tip (.cover 2 3 6)))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.tip (.zero 7)) (.tip (.cover 4 5 7))) (.split 8 (.split 11 (.split 13 (.tip (.zero 7)) (.tip (.unordered 5 1))) (.tip (.cover 0 5 7))) (.tip (.cover 2 3 6)))) (.tip (.cover 0 1 7)))))
private theorem q8Shape5T39OK : treeOK (forms 5) 70 681 q8Shape5T39=true := by decide

private def q8Shape5T40 : Tree := (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 5)) (.split 11 (.split 13 (.tip (.equal 2 5)) (.tip (.equal 2 3))) (.tip (.cover 0 3 4)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 5)) (.tip (.equal 2 5))) (.tip (.equal 3 4))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 1 7))) (.tip (.unordered 5 1))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 5)) (.split 11 (.split 13 (.tip (.equal 2 5)) (.tip (.equal 2 3))) (.tip (.cover 2 3 4)))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.cover 2 3 4))) (.tip (.cover 2 3 4)))) (.tip (.cover 0 1 7))) (.tip (.unordered 5 1))))
private theorem q8Shape5T40OK : treeOK (forms 5) 198 553 q8Shape5T40=true := by decide

private def q8Shape5T38 : Tree := .split 7 q8Shape5T39 q8Shape5T40
private theorem q8Shape5T38OK : treeOK (forms 5) 70 553 q8Shape5T38=true := by
  change (treeOK (forms 5) 70 (553 ||| 2^7) q8Shape5T39 &&
    treeOK (forms 5) (70 ||| 2^7) 553 q8Shape5T40)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T39OK,q8Shape5T40OK⟩

private def q8Shape5T41 : Tree := (.split 7 (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 3 4)) (.tip (.cover 0 2 7))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.unordered 2 1))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 1 7))) (.tip (.unordered 2 1))) (.tip (.unordered 2 1))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.zero 7)) (.tip (.cover 0 2 7))) (.split 8 (.split 11 (.split 13 (.tip (.zero 7)) (.tip (.unordered 2 1))) (.tip (.unordered 2 1))) (.tip (.cover 2 3 4)))) (.tip (.cover 0 1 7))) (.tip (.unordered 2 1))) (.tip (.unordered 2 1))))
private theorem q8Shape5T41OK : treeOK (forms 5) 78 545 q8Shape5T41=true := by decide

private def q8Shape5T37 : Tree := .split 3 q8Shape5T38 q8Shape5T41
private theorem q8Shape5T37OK : treeOK (forms 5) 70 545 q8Shape5T37=true := by
  change (treeOK (forms 5) 70 (545 ||| 2^3) q8Shape5T38 &&
    treeOK (forms 5) (70 ||| 2^3) 545 q8Shape5T41)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T38OK,q8Shape5T41OK⟩

private def q8Shape5T42 : Tree := (.tip (.unordered 5 1))
private theorem q8Shape5T42OK : treeOK (forms 5) 582 33 q8Shape5T42=true := by decide

private def q8Shape5T36 : Tree := .split 9 q8Shape5T37 q8Shape5T42
private theorem q8Shape5T36OK : treeOK (forms 5) 70 33 q8Shape5T36=true := by
  change (treeOK (forms 5) 70 (33 ||| 2^9) q8Shape5T37 &&
    treeOK (forms 5) (70 ||| 2^9) 33 q8Shape5T42)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T37OK,q8Shape5T42OK⟩

private def q8Shape5T34 : Tree := .split 6 q8Shape5T35 q8Shape5T36
private theorem q8Shape5T34OK : treeOK (forms 5) 6 33 q8Shape5T34=true := by
  change (treeOK (forms 5) 6 (33 ||| 2^6) q8Shape5T35 &&
    treeOK (forms 5) (6 ||| 2^6) 33 q8Shape5T36)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T35OK,q8Shape5T36OK⟩

private def q8Shape5T47 : Tree := (.split 10 (.split 12 (.tip (.equal 0 1)) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 4)) (.split 11 (.tip (.equal 2 4)) (.tip (.equal 3 5)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 4)) (.tip (.equal 4 5))) (.split 13 (.tip (.equal 2 4)) (.tip (.unordered 2 1)))) (.tip (.cover 2 3 6)))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 3 5)) (.split 11 (.tip (.equal 3 5)) (.tip (.unordered 4 1)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 3 5)) (.tip (.equal 2 4))) (.tip (.unordered 4 1))) (.split 11 (.split 13 (.tip (.equal 3 5)) (.tip (.equal 2 4))) (.tip (.unordered 4 0))))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.tip (.zero 7)) (.tip (.cover 4 5 7))) (.split 8 (.split 11 (.split 13 (.tip (.zero 7)) (.tip (.equal 2 4))) (.tip (.unordered 4 1))) (.tip (.cover 2 3 6)))) (.tip (.cover 0 1 7)))))
private theorem q8Shape5T47OK : treeOK (forms 5) 38 713 q8Shape5T47=true := by decide

private def q8Shape5T48 : Tree := (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 4)) (.split 11 (.tip (.equal 2 4)) (.tip (.equal 2 3)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 4)) (.tip (.equal 3 5))) (.split 13 (.tip (.equal 2 4)) (.tip (.unordered 2 1)))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 4)) (.split 11 (.tip (.equal 2 4)) (.tip (.equal 2 3)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 4)) (.tip (.equal 4 5))) (.tip (.cover 2 4 6))) (.tip (.cover 2 3 5)))) (.tip (.cover 0 1 7)))) (.tip (.unordered 4 1)))
private theorem q8Shape5T48OK : treeOK (forms 5) 166 585 q8Shape5T48=true := by decide

private def q8Shape5T46 : Tree := .split 7 q8Shape5T47 q8Shape5T48
private theorem q8Shape5T46OK : treeOK (forms 5) 38 585 q8Shape5T46=true := by
  change (treeOK (forms 5) 38 (585 ||| 2^7) q8Shape5T47 &&
    treeOK (forms 5) (38 ||| 2^7) 585 q8Shape5T48)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T47OK,q8Shape5T48OK⟩

private def q8Shape5T49 : Tree := (.split 7 (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 3 5)) (.tip (.cover 0 2 7))) (.split 8 (.split 11 (.split 13 (.tip (.equal 3 5)) (.tip (.unordered 2 1))) (.tip (.unordered 2 1))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 1 7))) (.tip (.unordered 2 1))) (.tip (.unordered 2 1))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.zero 7)) (.tip (.cover 0 2 7))) (.split 8 (.split 11 (.split 13 (.tip (.zero 7)) (.tip (.unordered 2 1))) (.tip (.unordered 2 1))) (.tip (.cover 2 3 5)))) (.tip (.cover 0 1 7))) (.tip (.unordered 2 1))) (.tip (.unordered 2 1))))
private theorem q8Shape5T49OK : treeOK (forms 5) 46 577 q8Shape5T49=true := by decide

private def q8Shape5T45 : Tree := .split 3 q8Shape5T46 q8Shape5T49
private theorem q8Shape5T45OK : treeOK (forms 5) 38 577 q8Shape5T45=true := by
  change (treeOK (forms 5) 38 (577 ||| 2^3) q8Shape5T46 &&
    treeOK (forms 5) (38 ||| 2^3) 577 q8Shape5T49)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T46OK,q8Shape5T49OK⟩

private def q8Shape5T50 : Tree := (.tip (.unordered 4 1))
private theorem q8Shape5T50OK : treeOK (forms 5) 550 65 q8Shape5T50=true := by decide

private def q8Shape5T44 : Tree := .split 9 q8Shape5T45 q8Shape5T50
private theorem q8Shape5T44OK : treeOK (forms 5) 38 65 q8Shape5T44=true := by
  change (treeOK (forms 5) 38 (65 ||| 2^9) q8Shape5T45 &&
    treeOK (forms 5) (38 ||| 2^9) 65 q8Shape5T50)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T45OK,q8Shape5T50OK⟩

private def q8Shape5T53 : Tree := (.split 7 (.split 10 (.split 12 (.tip (.equal 0 1)) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.tip (.equal 2 4)) (.tip (.cover 0 5 7)))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.cover 0 5 7))) (.tip (.cover 2 3 6)))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.equal 3 4))) (.tip (.cover 0 3 4)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.equal 2 4))) (.tip (.cover 0 2 4))) (.tip (.cover 2 3 6)))) (.tip (.cover 0 1 7))) (.tip (.cover 4 5 7)))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 4)) (.split 11 (.tip (.equal 2 4)) (.tip (.cover 0 3 4)))) (.tip (.cover 0 3 7))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 4)) (.split 11 (.tip (.equal 2 4)) (.tip (.unordered 3 1)))) (.tip (.cover 0 3 7))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 5)) (.split 11 (.split 13 (.tip (.equal 2 5)) (.tip (.unordered 3 1))) (.tip (.unordered 3 1)))) (.tip (.cover 0 3 7))) (.tip (.cover 0 1 7))) (.tip (.unordered 3 1)))))
private theorem q8Shape5T53OK : treeOK (forms 5) 102 521 q8Shape5T53=true := by decide

private def q8Shape5T54 : Tree := (.split 7 (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 3 4)) (.tip (.cover 0 2 7))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.cover 0 2 4))) (.tip (.cover 2 3 6)))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 5)) (.tip (.cover 0 2 7))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.unordered 2 1))) (.tip (.cover 2 3 5)))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 4)) (.tip (.cover 0 2 7))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 4)) (.tip (.unordered 2 1))) (.tip (.unordered 2 1))) (.tip (.cover 2 3 4)))) (.tip (.cover 0 1 7))) (.tip (.unordered 2 1)))) (.tip (.cover 2 3 7)))
private theorem q8Shape5T54OK : treeOK (forms 5) 110 513 q8Shape5T54=true := by decide

private def q8Shape5T52 : Tree := .split 3 q8Shape5T53 q8Shape5T54
private theorem q8Shape5T52OK : treeOK (forms 5) 102 513 q8Shape5T52=true := by
  change (treeOK (forms 5) 102 (513 ||| 2^3) q8Shape5T53 &&
    treeOK (forms 5) (102 ||| 2^3) 513 q8Shape5T54)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T53OK,q8Shape5T54OK⟩

private def q8Shape5T55 : Tree := (.tip (.unordered 4 1))
private theorem q8Shape5T55OK : treeOK (forms 5) 614 1 q8Shape5T55=true := by decide

private def q8Shape5T51 : Tree := .split 9 q8Shape5T52 q8Shape5T55
private theorem q8Shape5T51OK : treeOK (forms 5) 102 1 q8Shape5T51=true := by
  change (treeOK (forms 5) 102 (1 ||| 2^9) q8Shape5T52 &&
    treeOK (forms 5) (102 ||| 2^9) 1 q8Shape5T55)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T52OK,q8Shape5T55OK⟩

private def q8Shape5T43 : Tree := .split 6 q8Shape5T44 q8Shape5T51
private theorem q8Shape5T43OK : treeOK (forms 5) 38 1 q8Shape5T43=true := by
  change (treeOK (forms 5) 38 (1 ||| 2^6) q8Shape5T44 &&
    treeOK (forms 5) (38 ||| 2^6) 1 q8Shape5T51)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T44OK,q8Shape5T51OK⟩

private def q8Shape5T33 : Tree := .split 5 q8Shape5T34 q8Shape5T43
private theorem q8Shape5T33OK : treeOK (forms 5) 6 1 q8Shape5T33=true := by
  change (treeOK (forms 5) 6 (1 ||| 2^5) q8Shape5T34 &&
    treeOK (forms 5) (6 ||| 2^5) 1 q8Shape5T43)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T34OK,q8Shape5T43OK⟩

private def q8Shape5T17 : Tree := .split 2 q8Shape5T18 q8Shape5T33
private theorem q8Shape5T17OK : treeOK (forms 5) 2 1 q8Shape5T17=true := by
  change (treeOK (forms 5) 2 (1 ||| 2^2) q8Shape5T18 &&
    treeOK (forms 5) (2 ||| 2^2) 1 q8Shape5T33)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T18OK,q8Shape5T33OK⟩

private def q8Shape5T1 : Tree := .split 1 q8Shape5T2 q8Shape5T17
private theorem q8Shape5T1OK : treeOK (forms 5) 0 1 q8Shape5T1=true := by
  change (treeOK (forms 5) 0 (1 ||| 2^1) q8Shape5T2 &&
    treeOK (forms 5) (0 ||| 2^1) 1 q8Shape5T17)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T2OK,q8Shape5T17OK⟩

private def q8Shape5T60 : Tree := (.tip (.small 1))
private theorem q8Shape5T60OK : treeOK (forms 5) 1 102 q8Shape5T60=true := by decide

private def q8Shape5T62 : Tree := (.tip (.small 1))
private theorem q8Shape5T62OK : treeOK (forms 5) 65 550 q8Shape5T62=true := by decide

private def q8Shape5T64 : Tree := (.split 7 (.split 10 (.split 12 (.tip (.equal 0 1)) (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 4)) (.split 13 (.tip (.equal 2 4)) (.tip (.unordered 5 1)))) (.split 11 (.tip (.equal 2 4)) (.split 13 (.tip (.equal 2 4)) (.tip (.unordered 5 0))))) (.tip (.cover 0 5 7))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 3 5)) (.split 13 (.tip (.equal 3 5)) (.tip (.equal 3 4)))) (.split 11 (.split 13 (.tip (.equal 3 5)) (.tip (.equal 3 5))) (.tip (.cover 0 3 4)))) (.split 8 (.split 11 (.tip (.equal 3 5)) (.tip (.cover 0 2 4))) (.tip (.cover 0 4 7)))) (.tip (.cover 0 1 7))) (.tip (.unordered 5 1)))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 4)) (.tip (.cover 0 3 7))) (.split 11 (.tip (.equal 2 4)) (.tip (.cover 0 3 4)))) (.split 8 (.split 11 (.tip (.equal 2 4)) (.tip (.cover 0 3 7))) (.tip (.unordered 3 1)))) (.tip (.cover 0 1 7))) (.tip (.unordered 3 1))) (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.zero 7)) (.tip (.cover 0 3 7))) (.split 11 (.split 13 (.tip (.zero 7)) (.tip (.unordered 3 1))) (.tip (.cover 2 3 4)))) (.tip (.cover 3 4 7))) (.tip (.cover 0 1 7))) (.tip (.unordered 3 1)))))
private theorem q8Shape5T64OK : treeOK (forms 5) 577 46 q8Shape5T64=true := by decide

private def q8Shape5T65 : Tree := (.split 7 (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 3 5)) (.split 13 (.tip (.equal 3 5)) (.tip (.equal 2 4)))) (.split 11 (.split 13 (.tip (.equal 3 5)) (.tip (.equal 3 5))) (.tip (.cover 3 4 6)))) (.split 8 (.split 11 (.tip (.equal 3 5)) (.tip (.cover 0 2 4))) (.split 11 (.split 13 (.tip (.equal 2 5)) (.tip (.unordered 3 1))) (.tip (.cover 3 4 6))))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.zero 7)) (.tip (.cover 2 5 7))) (.split 11 (.split 13 (.tip (.zero 7)) (.tip (.unordered 5 1))) (.tip (.cover 2 5 7)))) (.tip (.cover 0 5 7))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 4)) (.split 13 (.tip (.equal 2 4)) (.tip (.equal 3 4)))) (.split 11 (.tip (.equal 2 4)) (.tip (.cover 2 3 4)))) (.split 8 (.split 11 (.tip (.equal 2 4)) (.tip (.cover 2 3 4))) (.tip (.cover 2 3 4)))) (.tip (.cover 0 1 7))) (.tip (.unordered 5 1)))) (.tip (.unordered 3 1)))
private theorem q8Shape5T65OK : treeOK (forms 5) 585 38 q8Shape5T65=true := by decide

private def q8Shape5T63 : Tree := .split 3 q8Shape5T64 q8Shape5T65
private theorem q8Shape5T63OK : treeOK (forms 5) 577 38 q8Shape5T63=true := by
  change (treeOK (forms 5) 577 (38 ||| 2^3) q8Shape5T64 &&
    treeOK (forms 5) (577 ||| 2^3) 38 q8Shape5T65)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T64OK,q8Shape5T65OK⟩

private def q8Shape5T61 : Tree := .split 9 q8Shape5T62 q8Shape5T63
private theorem q8Shape5T61OK : treeOK (forms 5) 65 38 q8Shape5T61=true := by
  change (treeOK (forms 5) 65 (38 ||| 2^9) q8Shape5T62 &&
    treeOK (forms 5) (65 ||| 2^9) 38 q8Shape5T63)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T62OK,q8Shape5T63OK⟩

private def q8Shape5T59 : Tree := .split 6 q8Shape5T60 q8Shape5T61
private theorem q8Shape5T59OK : treeOK (forms 5) 1 38 q8Shape5T59=true := by
  change (treeOK (forms 5) 1 (38 ||| 2^6) q8Shape5T60 &&
    treeOK (forms 5) (1 ||| 2^6) 38 q8Shape5T61)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T60OK,q8Shape5T61OK⟩

private def q8Shape5T68 : Tree := (.tip (.small 1))
private theorem q8Shape5T68OK : treeOK (forms 5) 33 582 q8Shape5T68=true := by decide

private def q8Shape5T70 : Tree := (.split 7 (.split 10 (.split 12 (.tip (.equal 0 1)) (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 3 4)) (.split 13 (.tip (.equal 3 4)) (.tip (.equal 3 5)))) (.split 11 (.tip (.equal 3 4)) (.split 13 (.tip (.equal 3 4)) (.tip (.unordered 4 1))))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.cover 2 4 6))) (.tip (.cover 0 5 7)))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 5)) (.split 13 (.tip (.equal 2 5)) (.tip (.unordered 4 1)))) (.split 11 (.tip (.equal 2 5)) (.tip (.unordered 4 1)))) (.tip (.cover 0 4 7))) (.tip (.cover 0 1 7))) (.tip (.unordered 4 1)))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 5)) (.split 13 (.tip (.equal 2 5)) (.tip (.equal 3 4)))) (.split 11 (.tip (.equal 2 5)) (.tip (.unordered 3 1)))) (.split 8 (.split 11 (.tip (.equal 2 5)) (.split 13 (.tip (.equal 2 5)) (.tip (.equal 3 4)))) (.tip (.unordered 3 1)))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.zero 7)) (.split 13 (.tip (.zero 7)) (.tip (.equal 3 4)))) (.split 11 (.tip (.zero 7)) (.tip (.unordered 3 1)))) (.tip (.cover 3 5 7))) (.tip (.cover 0 1 7)))) (.tip (.unordered 3 1))))
private theorem q8Shape5T70OK : treeOK (forms 5) 545 78 q8Shape5T70=true := by decide

private def q8Shape5T71 : Tree := (.split 7 (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 3 4)) (.split 13 (.tip (.equal 3 4)) (.tip (.equal 2 5)))) (.split 11 (.tip (.equal 3 4)) (.split 13 (.tip (.equal 3 4)) (.tip (.unordered 4 1))))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.cover 0 2 4))) (.split 11 (.tip (.equal 2 4)) (.tip (.unordered 3 1))))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 5)) (.split 13 (.tip (.equal 2 5)) (.tip (.equal 3 5)))) (.split 11 (.tip (.equal 2 5)) (.tip (.cover 2 5 7)))) (.split 8 (.split 11 (.tip (.equal 2 5)) (.tip (.cover 2 4 5))) (.tip (.cover 2 3 5)))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.zero 7)) (.split 13 (.tip (.zero 7)) (.tip (.unordered 4 1)))) (.split 11 (.tip (.zero 7)) (.tip (.unordered 4 1)))) (.tip (.cover 0 4 7))) (.tip (.cover 0 1 7))) (.tip (.unordered 4 1)))) (.tip (.unordered 3 1)))
private theorem q8Shape5T71OK : treeOK (forms 5) 553 70 q8Shape5T71=true := by decide

private def q8Shape5T69 : Tree := .split 3 q8Shape5T70 q8Shape5T71
private theorem q8Shape5T69OK : treeOK (forms 5) 545 70 q8Shape5T69=true := by
  change (treeOK (forms 5) 545 (70 ||| 2^3) q8Shape5T70 &&
    treeOK (forms 5) (545 ||| 2^3) 70 q8Shape5T71)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T70OK,q8Shape5T71OK⟩

private def q8Shape5T67 : Tree := .split 9 q8Shape5T68 q8Shape5T69
private theorem q8Shape5T67OK : treeOK (forms 5) 33 70 q8Shape5T67=true := by
  change (treeOK (forms 5) 33 (70 ||| 2^9) q8Shape5T68 &&
    treeOK (forms 5) (33 ||| 2^9) 70 q8Shape5T69)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T68OK,q8Shape5T69OK⟩

private def q8Shape5T72 : Tree := (.split 9 (.tip (.unordered 3 1)) (.tip (.unordered 3 1)))
private theorem q8Shape5T72OK : treeOK (forms 5) 97 6 q8Shape5T72=true := by decide

private def q8Shape5T66 : Tree := .split 6 q8Shape5T67 q8Shape5T72
private theorem q8Shape5T66OK : treeOK (forms 5) 33 6 q8Shape5T66=true := by
  change (treeOK (forms 5) 33 (6 ||| 2^6) q8Shape5T67 &&
    treeOK (forms 5) (33 ||| 2^6) 6 q8Shape5T72)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T67OK,q8Shape5T72OK⟩

private def q8Shape5T58 : Tree := .split 5 q8Shape5T59 q8Shape5T66
private theorem q8Shape5T58OK : treeOK (forms 5) 1 6 q8Shape5T58=true := by
  change (treeOK (forms 5) 1 (6 ||| 2^5) q8Shape5T59 &&
    treeOK (forms 5) (1 ||| 2^5) 6 q8Shape5T66)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T59OK,q8Shape5T66OK⟩

private def q8Shape5T76 : Tree := (.tip (.small 1))
private theorem q8Shape5T76OK : treeOK (forms 5) 5 610 q8Shape5T76=true := by decide

private def q8Shape5T79 : Tree := (.split 10 (.split 12 (.tip (.equal 0 1)) (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 3 4)) (.split 13 (.tip (.equal 3 4)) (.tip (.unordered 5 1)))) (.tip (.cover 0 5 7))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.split 13 (.tip (.equal 3 4)) (.tip (.unordered 5 0)))) (.tip (.cover 0 5 7)))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 5)) (.split 13 (.tip (.equal 2 5)) (.tip (.equal 2 4)))) (.split 11 (.tip (.equal 2 5)) (.tip (.cover 0 3 4)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 5)) (.tip (.equal 2 5))) (.tip (.cover 0 2 4))) (.tip (.cover 0 4 7)))) (.tip (.cover 0 1 7))) (.tip (.unordered 5 1))))
private theorem q8Shape5T79OK : treeOK (forms 5) 517 234 q8Shape5T79=true := by decide

private def q8Shape5T80 : Tree := (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 5)) (.split 13 (.tip (.equal 2 5)) (.tip (.equal 3 4)))) (.split 11 (.tip (.equal 2 5)) (.tip (.cover 0 3 4)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 5)) (.tip (.equal 2 5))) (.tip (.cover 2 4 6))) (.split 11 (.split 13 (.tip (.equal 3 5)) (.tip (.unordered 2 1))) (.tip (.cover 2 4 6))))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.zero 7)) (.tip (.cover 3 5 7))) (.tip (.cover 0 5 7))) (.split 8 (.split 11 (.split 13 (.tip (.zero 7)) (.tip (.unordered 5 1))) (.tip (.cover 2 4 6))) (.tip (.cover 0 5 7)))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 5)) (.split 13 (.tip (.equal 2 5)) (.tip (.equal 2 4)))) (.split 11 (.tip (.equal 2 5)) (.tip (.cover 2 3 4)))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.cover 2 3 4))) (.tip (.cover 2 3 4)))) (.tip (.cover 0 1 7))) (.tip (.unordered 5 1))))
private theorem q8Shape5T80OK : treeOK (forms 5) 645 106 q8Shape5T80=true := by decide

private def q8Shape5T78 : Tree := .split 7 q8Shape5T79 q8Shape5T80
private theorem q8Shape5T78OK : treeOK (forms 5) 517 106 q8Shape5T78=true := by
  change (treeOK (forms 5) 517 (106 ||| 2^7) q8Shape5T79 &&
    treeOK (forms 5) (517 ||| 2^7) 106 q8Shape5T80)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T79OK,q8Shape5T80OK⟩

private def q8Shape5T81 : Tree := (.split 7 (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.cover 0 2 7))) (.split 11 (.tip (.equal 3 4)) (.tip (.cover 0 2 7)))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.cover 0 2 4))) (.tip (.unordered 2 1)))) (.tip (.cover 0 1 7))) (.tip (.unordered 2 1))) (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.zero 7)) (.tip (.cover 0 2 7))) (.tip (.cover 2 4 7))) (.split 8 (.split 11 (.split 13 (.tip (.zero 7)) (.tip (.unordered 2 1))) (.tip (.cover 2 3 4))) (.tip (.unordered 2 1)))) (.tip (.cover 0 1 7))) (.tip (.unordered 2 1)))) (.tip (.unordered 2 1)))
private theorem q8Shape5T81OK : treeOK (forms 5) 525 98 q8Shape5T81=true := by decide

private def q8Shape5T77 : Tree := .split 3 q8Shape5T78 q8Shape5T81
private theorem q8Shape5T77OK : treeOK (forms 5) 517 98 q8Shape5T77=true := by
  change (treeOK (forms 5) 517 (98 ||| 2^3) q8Shape5T78 &&
    treeOK (forms 5) (517 ||| 2^3) 98 q8Shape5T81)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T78OK,q8Shape5T81OK⟩

private def q8Shape5T75 : Tree := .split 9 q8Shape5T76 q8Shape5T77
private theorem q8Shape5T75OK : treeOK (forms 5) 5 98 q8Shape5T75=true := by
  change (treeOK (forms 5) 5 (98 ||| 2^9) q8Shape5T76 &&
    treeOK (forms 5) (5 ||| 2^9) 98 q8Shape5T77)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T76OK,q8Shape5T77OK⟩

private def q8Shape5T82 : Tree := (.split 9 (.split 3 (.split 7 (.split 10 (.split 12 (.tip (.equal 0 1)) (.tip (.unordered 5 1))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.unordered 3 1))) (.tip (.cover 0 3 4)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.unordered 2 1))) (.tip (.cover 0 2 4))) (.tip (.unordered 2 1)))) (.tip (.cover 0 1 7))) (.tip (.unordered 5 1)))) (.tip (.unordered 3 1))) (.tip (.unordered 2 1))) (.tip (.unordered 5 1)))
private theorem q8Shape5T82OK : treeOK (forms 5) 69 34 q8Shape5T82=true := by decide

private def q8Shape5T74 : Tree := .split 6 q8Shape5T75 q8Shape5T82
private theorem q8Shape5T74OK : treeOK (forms 5) 5 34 q8Shape5T74=true := by
  change (treeOK (forms 5) 5 (34 ||| 2^6) q8Shape5T75 &&
    treeOK (forms 5) (5 ||| 2^6) 34 q8Shape5T82)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T75OK,q8Shape5T82OK⟩

private def q8Shape5T87 : Tree := (.split 10 (.split 12 (.tip (.equal 0 1)) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.tip (.equal 2 3)) (.tip (.equal 4 5)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.equal 3 5))) (.tip (.cover 2 4 6))) (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.unordered 2 1))) (.tip (.unordered 3 1))))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.tip (.equal 2 3)) (.tip (.equal 2 4)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.equal 4 5))) (.tip (.cover 0 2 4))) (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.unordered 2 1))) (.tip (.unordered 3 1))))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.tip (.equal 2 3)) (.tip (.equal 2 4)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.equal 3 5))) (.tip (.cover 2 4 5))) (.tip (.cover 2 3 6)))) (.tip (.cover 0 1 7)))))
private theorem q8Shape5T87OK : treeOK (forms 5) 37 714 q8Shape5T87=true := by decide

private def q8Shape5T88 : Tree := (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 4 5)) (.split 11 (.tip (.equal 4 5)) (.tip (.unordered 3 1)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 4 5)) (.tip (.equal 2 3))) (.split 13 (.tip (.equal 4 5)) (.tip (.equal 2 3)))) (.tip (.unordered 3 1)))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.tip (.zero 7)) (.split 11 (.tip (.zero 7)) (.tip (.unordered 3 1)))) (.split 8 (.split 11 (.split 13 (.tip (.zero 7)) (.tip (.equal 2 3))) (.tip (.cover 2 4 6))) (.tip (.unordered 3 1)))) (.tip (.cover 0 1 7)))) (.tip (.unordered 3 1)))
private theorem q8Shape5T88OK : treeOK (forms 5) 165 586 q8Shape5T88=true := by decide

private def q8Shape5T86 : Tree := .split 7 q8Shape5T87 q8Shape5T88
private theorem q8Shape5T86OK : treeOK (forms 5) 37 586 q8Shape5T86=true := by
  change (treeOK (forms 5) 37 (586 ||| 2^7) q8Shape5T87 &&
    treeOK (forms 5) (37 ||| 2^7) 586 q8Shape5T88)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T87OK,q8Shape5T88OK⟩

private def q8Shape5T89 : Tree := (.split 7 (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 4 5)) (.split 11 (.tip (.equal 4 5)) (.tip (.equal 2 3)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 4 5)) (.tip (.unordered 2 1))) (.tip (.cover 0 2 4))) (.tip (.unordered 2 1)))) (.tip (.cover 0 1 7))) (.tip (.unordered 2 1))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.zero 7)) (.split 11 (.tip (.zero 7)) (.tip (.equal 2 3)))) (.split 8 (.split 11 (.split 13 (.tip (.zero 7)) (.tip (.unordered 2 1))) (.tip (.cover 2 4 5))) (.tip (.unordered 2 1)))) (.tip (.cover 0 1 7))) (.tip (.unordered 2 1)))) (.tip (.unordered 2 1)))
private theorem q8Shape5T89OK : treeOK (forms 5) 45 578 q8Shape5T89=true := by decide

private def q8Shape5T85 : Tree := .split 3 q8Shape5T86 q8Shape5T89
private theorem q8Shape5T85OK : treeOK (forms 5) 37 578 q8Shape5T85=true := by
  change (treeOK (forms 5) 37 (578 ||| 2^3) q8Shape5T86 &&
    treeOK (forms 5) (37 ||| 2^3) 578 q8Shape5T89)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T86OK,q8Shape5T89OK⟩

private def q8Shape5T91 : Tree := (.split 7 (.split 10 (.split 12 (.tip (.equal 0 1)) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.tip (.cover 0 5 7))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.cover 2 4 6))) (.tip (.cover 0 5 7)))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.tip (.equal 2 3)) (.tip (.cover 0 3 4)))) (.tip (.cover 0 4 7))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.tip (.cover 0 5 7))) (.tip (.cover 0 4 7))) (.tip (.cover 0 1 7))))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 4)) (.split 13 (.tip (.equal 2 4)) (.tip (.equal 3 4)))) (.split 11 (.tip (.equal 2 4)) (.tip (.cover 0 3 4)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 4)) (.tip (.equal 2 3))) (.tip (.cover 2 4 6))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 1 7))) (.tip (.cover 3 5 7))) (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 5)) (.split 13 (.tip (.equal 2 5)) (.tip (.unordered 4 1)))) (.split 11 (.tip (.equal 2 5)) (.tip (.unordered 3 1)))) (.tip (.cover 0 4 7))) (.tip (.cover 0 1 7))) (.tip (.unordered 4 1)))))
private theorem q8Shape5T91OK : treeOK (forms 5) 549 74 q8Shape5T91=true := by decide

private def q8Shape5T92 : Tree := (.split 7 (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.cover 0 2 7))) (.split 11 (.tip (.equal 3 4)) (.tip (.equal 2 3)))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.cover 2 4 6))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 5)) (.tip (.cover 0 2 7))) (.tip (.cover 0 5 7))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.cover 2 4 5))) (.tip (.unordered 2 1)))) (.tip (.cover 0 1 7)))) (.tip (.cover 2 4 7))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.tip (.equal 2 3)) (.tip (.unordered 3 1)))) (.split 8 (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.unordered 2 1))) (.tip (.cover 2 3 4))) (.tip (.unordered 2 1)))) (.tip (.cover 0 1 7))) (.tip (.unordered 2 1))) (.tip (.unordered 3 1))))
private theorem q8Shape5T92OK : treeOK (forms 5) 557 66 q8Shape5T92=true := by decide

private def q8Shape5T90 : Tree := .split 3 q8Shape5T91 q8Shape5T92
private theorem q8Shape5T90OK : treeOK (forms 5) 549 66 q8Shape5T90=true := by
  change (treeOK (forms 5) 549 (66 ||| 2^3) q8Shape5T91 &&
    treeOK (forms 5) (549 ||| 2^3) 66 q8Shape5T92)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T91OK,q8Shape5T92OK⟩

private def q8Shape5T84 : Tree := .split 9 q8Shape5T85 q8Shape5T90
private theorem q8Shape5T84OK : treeOK (forms 5) 37 66 q8Shape5T84=true := by
  change (treeOK (forms 5) 37 (66 ||| 2^9) q8Shape5T85 &&
    treeOK (forms 5) (37 ||| 2^9) 66 q8Shape5T90)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T85OK,q8Shape5T90OK⟩

private def q8Shape5T93 : Tree := (.split 9 (.tip (.unordered 3 1)) (.tip (.unordered 3 1)))
private theorem q8Shape5T93OK : treeOK (forms 5) 101 2 q8Shape5T93=true := by decide

private def q8Shape5T83 : Tree := .split 6 q8Shape5T84 q8Shape5T93
private theorem q8Shape5T83OK : treeOK (forms 5) 37 2 q8Shape5T83=true := by
  change (treeOK (forms 5) 37 (2 ||| 2^6) q8Shape5T84 &&
    treeOK (forms 5) (37 ||| 2^6) 2 q8Shape5T93)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T84OK,q8Shape5T93OK⟩

private def q8Shape5T73 : Tree := .split 5 q8Shape5T74 q8Shape5T83
private theorem q8Shape5T73OK : treeOK (forms 5) 5 2 q8Shape5T73=true := by
  change (treeOK (forms 5) 5 (2 ||| 2^5) q8Shape5T74 &&
    treeOK (forms 5) (5 ||| 2^5) 2 q8Shape5T83)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T74OK,q8Shape5T83OK⟩

private def q8Shape5T57 : Tree := .split 2 q8Shape5T58 q8Shape5T73
private theorem q8Shape5T57OK : treeOK (forms 5) 1 2 q8Shape5T57=true := by
  change (treeOK (forms 5) 1 (2 ||| 2^2) q8Shape5T58 &&
    treeOK (forms 5) (1 ||| 2^2) 2 q8Shape5T73)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T58OK,q8Shape5T73OK⟩

private def q8Shape5T98 : Tree := (.tip (.small 1))
private theorem q8Shape5T98OK : treeOK (forms 5) 3 612 q8Shape5T98=true := by decide

private def q8Shape5T101 : Tree := (.split 10 (.split 12 (.tip (.equal 0 1)) (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 4)) (.split 13 (.tip (.equal 2 4)) (.tip (.equal 2 5)))) (.split 11 (.tip (.equal 2 4)) (.tip (.cover 3 4 6)))) (.split 8 (.split 11 (.tip (.equal 2 4)) (.split 13 (.tip (.equal 2 4)) (.tip (.unordered 4 1)))) (.tip (.cover 0 5 7)))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 3 5)) (.split 13 (.tip (.equal 3 5)) (.tip (.unordered 4 1)))) (.tip (.cover 0 4 7))) (.split 8 (.split 11 (.tip (.equal 3 5)) (.tip (.unordered 4 1))) (.tip (.cover 0 4 7)))) (.tip (.cover 0 1 7))) (.tip (.unordered 4 1))))
private theorem q8Shape5T101OK : treeOK (forms 5) 515 236 q8Shape5T101=true := by decide

private def q8Shape5T102 : Tree := (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 4)) (.split 13 (.tip (.equal 2 4)) (.tip (.equal 3 5)))) (.split 11 (.tip (.equal 2 4)) (.tip (.cover 0 3 4)))) (.split 8 (.split 11 (.tip (.equal 2 4)) (.split 13 (.tip (.equal 2 4)) (.tip (.unordered 4 1)))) (.split 11 (.tip (.equal 3 4)) (.tip (.unordered 2 1))))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 4)) (.split 13 (.tip (.equal 2 4)) (.tip (.equal 2 5)))) (.split 11 (.tip (.equal 2 4)) (.tip (.cover 3 4 5)))) (.split 8 (.split 11 (.tip (.equal 2 4)) (.tip (.cover 2 4 6))) (.tip (.cover 2 3 5)))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.zero 7)) (.split 13 (.tip (.zero 7)) (.tip (.unordered 4 1)))) (.tip (.cover 0 4 7))) (.split 8 (.split 11 (.tip (.zero 7)) (.tip (.unordered 4 1))) (.tip (.cover 0 4 7)))) (.tip (.cover 0 1 7))) (.tip (.unordered 4 1))))
private theorem q8Shape5T102OK : treeOK (forms 5) 643 108 q8Shape5T102=true := by decide

private def q8Shape5T100 : Tree := .split 7 q8Shape5T101 q8Shape5T102
private theorem q8Shape5T100OK : treeOK (forms 5) 515 108 q8Shape5T100=true := by
  change (treeOK (forms 5) 515 (108 ||| 2^7) q8Shape5T101 &&
    treeOK (forms 5) (515 ||| 2^7) 108 q8Shape5T102)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T101OK,q8Shape5T102OK⟩

private def q8Shape5T103 : Tree := (.split 7 (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 3 5)) (.split 13 (.tip (.equal 3 5)) (.tip (.equal 2 4)))) (.split 11 (.tip (.equal 3 5)) (.split 13 (.tip (.equal 3 5)) (.tip (.equal 2 4))))) (.split 8 (.split 11 (.tip (.equal 3 5)) (.tip (.unordered 2 1))) (.tip (.unordered 2 1)))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.zero 7)) (.split 13 (.tip (.zero 7)) (.tip (.equal 2 4)))) (.tip (.cover 2 5 7))) (.split 8 (.split 11 (.tip (.zero 7)) (.tip (.unordered 2 1))) (.tip (.unordered 2 1)))) (.tip (.cover 0 1 7)))) (.tip (.unordered 2 1))) (.tip (.unordered 2 1)))
private theorem q8Shape5T103OK : treeOK (forms 5) 523 100 q8Shape5T103=true := by decide

private def q8Shape5T99 : Tree := .split 3 q8Shape5T100 q8Shape5T103
private theorem q8Shape5T99OK : treeOK (forms 5) 515 100 q8Shape5T99=true := by
  change (treeOK (forms 5) 515 (100 ||| 2^3) q8Shape5T100 &&
    treeOK (forms 5) (515 ||| 2^3) 100 q8Shape5T103)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T100OK,q8Shape5T103OK⟩

private def q8Shape5T97 : Tree := .split 9 q8Shape5T98 q8Shape5T99
private theorem q8Shape5T97OK : treeOK (forms 5) 3 100 q8Shape5T97=true := by
  change (treeOK (forms 5) 3 (100 ||| 2^9) q8Shape5T98 &&
    treeOK (forms 5) (3 ||| 2^9) 100 q8Shape5T99)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T98OK,q8Shape5T99OK⟩

private def q8Shape5T107 : Tree := (.split 10 (.split 12 (.tip (.equal 0 1)) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.equal 2 5))) (.tip (.cover 3 4 6)))) (.split 8 (.split 11 (.tip (.equal 2 3)) (.tip (.equal 4 5))) (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.unordered 3 1))) (.tip (.unordered 2 1))))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.equal 4 5))) (.tip (.cover 0 3 4)))) (.split 8 (.split 11 (.tip (.equal 2 3)) (.tip (.equal 3 4))) (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.unordered 3 1))) (.tip (.unordered 2 1))))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.equal 2 5))) (.tip (.cover 3 4 5)))) (.split 8 (.split 11 (.tip (.equal 2 3)) (.tip (.equal 3 4))) (.tip (.cover 2 3 6)))) (.tip (.cover 0 1 7)))))
private theorem q8Shape5T107OK : treeOK (forms 5) 67 684 q8Shape5T107=true := by decide

private def q8Shape5T108 : Tree := (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 4 5)) (.split 11 (.split 13 (.tip (.equal 4 5)) (.tip (.unordered 3 1))) (.tip (.cover 0 3 4)))) (.split 8 (.split 11 (.tip (.equal 4 5)) (.tip (.equal 2 3))) (.tip (.unordered 3 1)))) (.tip (.cover 0 1 7))) (.tip (.unordered 3 1))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.zero 7)) (.split 11 (.split 13 (.tip (.zero 7)) (.tip (.unordered 3 1))) (.tip (.cover 3 4 5)))) (.split 8 (.split 11 (.tip (.zero 7)) (.tip (.equal 2 3))) (.tip (.unordered 3 1)))) (.tip (.cover 0 1 7))) (.tip (.unordered 3 1))))
private theorem q8Shape5T108OK : treeOK (forms 5) 195 556 q8Shape5T108=true := by decide

private def q8Shape5T106 : Tree := .split 7 q8Shape5T107 q8Shape5T108
private theorem q8Shape5T106OK : treeOK (forms 5) 67 556 q8Shape5T106=true := by
  change (treeOK (forms 5) 67 (556 ||| 2^7) q8Shape5T107 &&
    treeOK (forms 5) (67 ||| 2^7) 556 q8Shape5T108)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T107OK,q8Shape5T108OK⟩

private def q8Shape5T109 : Tree := (.split 7 (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 4 5)) (.split 11 (.split 13 (.tip (.equal 4 5)) (.tip (.equal 2 3))) (.split 13 (.tip (.equal 4 5)) (.tip (.equal 2 3))))) (.split 8 (.split 11 (.tip (.equal 4 5)) (.tip (.unordered 2 1))) (.tip (.unordered 2 1)))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.tip (.zero 7)) (.split 11 (.split 13 (.tip (.zero 7)) (.tip (.equal 2 3))) (.tip (.cover 2 5 7)))) (.split 8 (.split 11 (.tip (.zero 7)) (.tip (.unordered 2 1))) (.tip (.unordered 2 1)))) (.tip (.cover 0 1 7)))) (.tip (.unordered 2 1))) (.tip (.unordered 2 1)))
private theorem q8Shape5T109OK : treeOK (forms 5) 75 548 q8Shape5T109=true := by decide

private def q8Shape5T105 : Tree := .split 3 q8Shape5T106 q8Shape5T109
private theorem q8Shape5T105OK : treeOK (forms 5) 67 548 q8Shape5T105=true := by
  change (treeOK (forms 5) 67 (548 ||| 2^3) q8Shape5T106 &&
    treeOK (forms 5) (67 ||| 2^3) 548 q8Shape5T109)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T106OK,q8Shape5T109OK⟩

private def q8Shape5T111 : Tree := (.split 7 (.split 10 (.split 12 (.tip (.equal 0 1)) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.tip (.equal 2 4)) (.tip (.cover 3 4 6)))) (.tip (.cover 0 5 7))) (.tip (.cover 0 1 7)))) (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.tip (.cover 0 4 7))) (.split 8 (.split 11 (.tip (.equal 2 3)) (.tip (.cover 0 2 4))) (.tip (.cover 0 4 7)))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.tip (.cover 0 4 7))) (.tip (.cover 0 5 7))) (.tip (.cover 0 1 7))))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 4)) (.tip (.cover 0 3 7))) (.split 11 (.tip (.equal 2 4)) (.tip (.cover 3 4 6)))) (.split 8 (.split 11 (.tip (.equal 2 4)) (.tip (.equal 2 3))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 1 7))) (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 4)) (.tip (.cover 0 3 7))) (.split 11 (.tip (.equal 2 4)) (.tip (.cover 3 4 5)))) (.tip (.cover 0 5 7))) (.tip (.cover 0 1 7)))) (.tip (.cover 3 4 7))))
private theorem q8Shape5T111OK : treeOK (forms 5) 579 44 q8Shape5T111=true := by decide

private def q8Shape5T112 : Tree := (.split 7 (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 3 4)) (.split 13 (.tip (.equal 3 4)) (.tip (.equal 2 4)))) (.split 11 (.split 13 (.tip (.equal 3 4)) (.tip (.equal 2 3))) (.tip (.cover 3 4 6)))) (.split 8 (.split 11 (.tip (.equal 3 4)) (.tip (.cover 0 2 4))) (.tip (.cover 0 2 3)))) (.tip (.cover 0 1 7))) (.tip (.cover 2 5 7))) (.split 12 (.split 14 (.split 4 (.split 8 (.split 11 (.tip (.equal 2 4)) (.split 13 (.tip (.equal 2 4)) (.tip (.unordered 4 1)))) (.tip (.cover 0 4 7))) (.split 8 (.split 11 (.tip (.equal 2 4)) (.tip (.unordered 2 1))) (.tip (.unordered 2 1)))) (.tip (.cover 0 1 7))) (.tip (.unordered 4 1)))) (.split 10 (.split 12 (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.split 13 (.tip (.equal 2 3)) (.tip (.unordered 3 1))) (.tip (.cover 2 3 4)))) (.split 8 (.split 11 (.tip (.equal 2 3)) (.tip (.unordered 2 1))) (.tip (.unordered 2 1)))) (.tip (.cover 0 1 7))) (.tip (.unordered 3 1))) (.tip (.unordered 2 1))))
private theorem q8Shape5T112OK : treeOK (forms 5) 587 36 q8Shape5T112=true := by decide

private def q8Shape5T110 : Tree := .split 3 q8Shape5T111 q8Shape5T112
private theorem q8Shape5T110OK : treeOK (forms 5) 579 36 q8Shape5T110=true := by
  change (treeOK (forms 5) 579 (36 ||| 2^3) q8Shape5T111 &&
    treeOK (forms 5) (579 ||| 2^3) 36 q8Shape5T112)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T111OK,q8Shape5T112OK⟩

private def q8Shape5T104 : Tree := .split 9 q8Shape5T105 q8Shape5T110
private theorem q8Shape5T104OK : treeOK (forms 5) 67 36 q8Shape5T104=true := by
  change (treeOK (forms 5) 67 (36 ||| 2^9) q8Shape5T105 &&
    treeOK (forms 5) (67 ||| 2^9) 36 q8Shape5T110)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T105OK,q8Shape5T110OK⟩

private def q8Shape5T96 : Tree := .split 6 q8Shape5T97 q8Shape5T104
private theorem q8Shape5T96OK : treeOK (forms 5) 3 36 q8Shape5T96=true := by
  change (treeOK (forms 5) 3 (36 ||| 2^6) q8Shape5T97 &&
    treeOK (forms 5) (3 ||| 2^6) 36 q8Shape5T104)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T97OK,q8Shape5T104OK⟩

private def q8Shape5T113 : Tree := (.split 6 (.split 9 (.split 3 (.split 7 (.split 10 (.split 12 (.tip (.equal 0 1)) (.split 14 (.split 4 (.split 8 (.tip (.equal 2 3)) (.split 11 (.tip (.equal 2 3)) (.tip (.unordered 3 1)))) (.split 8 (.split 11 (.tip (.equal 2 3)) (.tip (.unordered 2 1))) (.tip (.unordered 2 1)))) (.tip (.cover 0 1 7)))) (.tip (.unordered 4 1))) (.tip (.unordered 3 1))) (.tip (.unordered 2 1))) (.tip (.unordered 4 1))) (.split 9 (.tip (.unordered 3 1)) (.tip (.unordered 3 1))))
private theorem q8Shape5T113OK : treeOK (forms 5) 35 4 q8Shape5T113=true := by decide

private def q8Shape5T95 : Tree := .split 5 q8Shape5T96 q8Shape5T113
private theorem q8Shape5T95OK : treeOK (forms 5) 3 4 q8Shape5T95=true := by
  change (treeOK (forms 5) 3 (4 ||| 2^5) q8Shape5T96 &&
    treeOK (forms 5) (3 ||| 2^5) 4 q8Shape5T113)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T96OK,q8Shape5T113OK⟩

private def q8Shape5T114 : Tree := (.split 5 (.split 6 (.split 9 (.tip (.unordered 2 1)) (.tip (.unordered 2 1))) (.split 9 (.tip (.unordered 2 1)) (.tip (.unordered 2 1)))) (.split 6 (.split 9 (.tip (.unordered 2 1)) (.tip (.unordered 2 1))) (.split 9 (.tip (.unordered 2 1)) (.tip (.unordered 2 1)))))
private theorem q8Shape5T114OK : treeOK (forms 5) 7 0 q8Shape5T114=true := by decide

private def q8Shape5T94 : Tree := .split 2 q8Shape5T95 q8Shape5T114
private theorem q8Shape5T94OK : treeOK (forms 5) 3 0 q8Shape5T94=true := by
  change (treeOK (forms 5) 3 (0 ||| 2^2) q8Shape5T95 &&
    treeOK (forms 5) (3 ||| 2^2) 0 q8Shape5T114)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T95OK,q8Shape5T114OK⟩

private def q8Shape5T56 : Tree := .split 1 q8Shape5T57 q8Shape5T94
private theorem q8Shape5T56OK : treeOK (forms 5) 1 0 q8Shape5T56=true := by
  change (treeOK (forms 5) 1 (0 ||| 2^1) q8Shape5T57 &&
    treeOK (forms 5) (1 ||| 2^1) 0 q8Shape5T94)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T57OK,q8Shape5T94OK⟩

private def q8Shape5T0 : Tree := .split 0 q8Shape5T1 q8Shape5T56
private theorem q8Shape5T0OK : treeOK (forms 5) 0 0 q8Shape5T0=true := by
  change (treeOK (forms 5) 0 (0 ||| 2^0) q8Shape5T1 &&
    treeOK (forms 5) (0 ||| 2^0) 0 q8Shape5T56)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape5T1OK,q8Shape5T56OK⟩


theorem q8Shape5_cover (b : Nat→Bool) (H : Ranked (adj (forms 5) b)) :
    ∃ u v w,Dominates3 (adj (forms 5) b) u v w :=
  checked_tree (forms 5) b H q8Shape5T0 q8Shape5T0OK

#print axioms q8Shape5_cover
end Graffiti384b.Q8
