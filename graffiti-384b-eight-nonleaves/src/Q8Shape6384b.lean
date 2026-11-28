import Q8MaskKernel384b

namespace Graffiti384b.Q8
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
private def q8Shape6T5 : Tree := (.tip (.zero 7))
private theorem q8Shape6T5OK : treeOK (forms 6) 0 26896 q8Shape6T5=true := by decide

private def q8Shape6T7 : Tree := (.split 7 (.split 10 (.split 12 (.tip (.zero 6)) (.tip (.equal 6 7))) (.split 12 (.tip (.equal 6 7)) (.tip (.cover 0 1 5)))) (.split 10 (.split 12 (.tip (.equal 6 7)) (.tip (.cover 0 1 5))) (.split 12 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.tip (.cover 1 5 6))) (.split 2 (.split 5 (.split 6 (.tip (.equal 3 6)) (.split 9 (.tip (.equal 3 4)) (.tip (.equal 4 5)))) (.tip (.equal 2 6))) (.tip (.cover 1 5 6)))) (.split 1 (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 3 4))) (.split 9 (.tip (.equal 4 6)) (.tip (.equal 3 5)))) (.tip (.equal 2 6))) (.tip (.cover 1 5 6))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.equal 3 4)) (.tip (.equal 3 5))) (.tip (.cover 3 4 7))) (.tip (.cover 0 3 7))) (.tip (.cover 2 6 7))))) (.tip (.cover 0 1 5)))))
private theorem q8Shape6T7OK : treeOK (forms 6) 8192 18712 q8Shape6T7=true := by decide

private def q8Shape6T9 : Tree := (.split 10 (.split 12 (.tip (.equal 6 7)) (.tip (.cover 0 1 5))) (.split 12 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.split 5 (.split 6 (.tip (.equal 3 7)) (.tip (.cover 1 5 6))) (.split 6 (.split 9 (.tip (.equal 2 4)) (.tip (.equal 4 5))) (.tip (.cover 1 5 6))))) (.split 2 (.split 5 (.split 6 (.tip (.equal 3 7)) (.tip (.equal 3 6))) (.tip (.cover 0 4 7))) (.split 5 (.split 6 (.tip (.equal 3 7)) (.tip (.equal 3 6))) (.tip (.cover 0 4 7))))) (.split 1 (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 2 4))) (.tip (.cover 1 5 6))) (.split 6 (.split 9 (.tip (.equal 2 4)) (.tip (.equal 2 5))) (.tip (.cover 3 6 7)))) (.split 5 (.split 6 (.split 9 (.tip (.equal 4 6)) (.tip (.equal 2 5))) (.tip (.cover 1 5 6))) (.tip (.cover 2 4 7)))) (.tip (.cover 0 2 7)))) (.tip (.cover 0 1 5))))
private theorem q8Shape6T9OK : treeOK (forms 6) 8200 18832 q8Shape6T9=true := by decide

private def q8Shape6T10 : Tree := (.split 10 (.split 12 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.split 5 (.split 6 (.tip (.equal 3 6)) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.split 9 (.tip (.equal 3 5)) (.tip (.unordered 5 1)))))) (.split 2 (.split 5 (.split 6 (.tip (.equal 3 6)) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.tip (.cover 2 3 7)))) (.split 5 (.split 6 (.tip (.equal 3 6)) (.split 9 (.tip (.equal 2 5)) (.tip (.unordered 5 1)))) (.tip (.cover 2 3 7))))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.equal 2 3)) (.split 9 (.tip (.unordered 3 1)) (.tip (.equal 4 6)))) (.tip (.cover 0 3 7))) (.split 5 (.split 6 (.split 9 (.tip (.unordered 2 1)) (.tip (.equal 4 6))) (.tip (.equal 2 3))) (.tip (.cover 0 3 7)))) (.tip (.cover 0 2 7)))) (.tip (.cover 0 1 5))) (.tip (.cover 0 6 7)))
private theorem q8Shape6T10OK : treeOK (forms 6) 8328 18704 q8Shape6T10=true := by decide

private def q8Shape6T8 : Tree := .split 7 q8Shape6T9 q8Shape6T10
private theorem q8Shape6T8OK : treeOK (forms 6) 8200 18704 q8Shape6T8=true := by
  change (treeOK (forms 6) 8200 (18704 ||| 2^7) q8Shape6T9 &&
    treeOK (forms 6) (8200 ||| 2^7) 18704 q8Shape6T10)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T9OK,q8Shape6T10OK⟩

private def q8Shape6T6 : Tree := .split 3 q8Shape6T7 q8Shape6T8
private theorem q8Shape6T6OK : treeOK (forms 6) 8192 18704 q8Shape6T6=true := by
  change (treeOK (forms 6) 8192 (18704 ||| 2^3) q8Shape6T7 &&
    treeOK (forms 6) (8192 ||| 2^3) 18704 q8Shape6T8)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T7OK,q8Shape6T8OK⟩

private def q8Shape6T4 : Tree := .split 13 q8Shape6T5 q8Shape6T6
private theorem q8Shape6T4OK : treeOK (forms 6) 0 18704 q8Shape6T4=true := by
  change (treeOK (forms 6) 0 (18704 ||| 2^13) q8Shape6T5 &&
    treeOK (forms 6) (0 ||| 2^13) 18704 q8Shape6T6)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T5OK,q8Shape6T6OK⟩

private def q8Shape6T13 : Tree := (.split 7 (.split 10 (.split 12 (.tip (.zero 6)) (.tip (.equal 6 7))) (.tip (.cover 0 1 4))) (.split 10 (.split 12 (.tip (.equal 6 7)) (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.split 5 (.split 6 (.tip (.equal 3 6)) (.tip (.equal 2 6))) (.split 6 (.split 9 (.tip (.equal 3 4)) (.tip (.equal 4 5))) (.tip (.equal 2 6))))) (.tip (.cover 1 4 6))) (.split 1 (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 3 4))) (.tip (.equal 2 6))) (.split 6 (.split 9 (.tip (.equal 5 6)) (.tip (.equal 3 4))) (.tip (.unordered 3 1)))) (.split 5 (.split 6 (.split 9 (.tip (.equal 3 5)) (.tip (.equal 3 4))) (.tip (.cover 0 3 7))) (.tip (.cover 3 5 7)))) (.tip (.cover 1 4 6))))) (.tip (.cover 0 1 4))))
private theorem q8Shape6T13OK : treeOK (forms 6) 2048 24856 q8Shape6T13=true := by decide

private def q8Shape6T15 : Tree := (.split 10 (.split 12 (.tip (.equal 6 7)) (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.split 5 (.split 6 (.tip (.equal 3 7)) (.tip (.equal 3 6))) (.tip (.cover 1 4 6)))) (.split 2 (.split 5 (.split 6 (.tip (.equal 3 7)) (.split 9 (.tip (.equal 2 4)) (.tip (.equal 4 5)))) (.tip (.cover 1 4 6))) (.split 5 (.split 6 (.tip (.equal 3 7)) (.tip (.equal 3 6))) (.tip (.cover 1 4 6))))) (.split 1 (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.equal 2 4))) (.split 9 (.tip (.equal 2 5)) (.tip (.equal 2 4)))) (.tip (.cover 1 4 6))) (.tip (.cover 0 2 7))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.equal 5 6)) (.tip (.equal 2 4))) (.tip (.cover 2 5 7))) (.tip (.cover 1 4 6))) (.tip (.cover 0 2 7)))))) (.tip (.cover 0 1 4)))
private theorem q8Shape6T15OK : treeOK (forms 6) 2056 24976 q8Shape6T15=true := by decide

private def q8Shape6T16 : Tree := (.split 10 (.split 12 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.split 5 (.split 6 (.tip (.equal 3 6)) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.tip (.cover 2 3 7))))) (.split 2 (.split 5 (.split 6 (.tip (.equal 3 6)) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.split 9 (.tip (.equal 3 4)) (.tip (.unordered 4 1))))) (.split 5 (.split 6 (.tip (.equal 3 6)) (.tip (.cover 2 3 7))) (.split 6 (.split 9 (.tip (.equal 2 4)) (.tip (.unordered 4 1))) (.tip (.cover 2 3 7)))))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.equal 2 3)) (.tip (.cover 0 3 7))) (.split 6 (.split 9 (.tip (.unordered 3 1)) (.tip (.equal 5 6))) (.tip (.unordered 3 1)))) (.tip (.cover 0 2 7))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.unordered 2 1)) (.tip (.equal 5 6))) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.tip (.unordered 3 1)))) (.tip (.cover 0 2 7))))) (.tip (.cover 0 6 7))) (.tip (.cover 0 1 4)))
private theorem q8Shape6T16OK : treeOK (forms 6) 2184 24848 q8Shape6T16=true := by decide

private def q8Shape6T14 : Tree := .split 7 q8Shape6T15 q8Shape6T16
private theorem q8Shape6T14OK : treeOK (forms 6) 2056 24848 q8Shape6T14=true := by
  change (treeOK (forms 6) 2056 (24848 ||| 2^7) q8Shape6T15 &&
    treeOK (forms 6) (2056 ||| 2^7) 24848 q8Shape6T16)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T15OK,q8Shape6T16OK⟩

private def q8Shape6T12 : Tree := .split 3 q8Shape6T13 q8Shape6T14
private theorem q8Shape6T12OK : treeOK (forms 6) 2048 24848 q8Shape6T12=true := by
  change (treeOK (forms 6) 2048 (24848 ||| 2^3) q8Shape6T13 &&
    treeOK (forms 6) (2048 ||| 2^3) 24848 q8Shape6T14)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T13OK,q8Shape6T14OK⟩

private def q8Shape6T18 : Tree := (.split 7 (.split 10 (.split 12 (.tip (.zero 6)) (.tip (.cover 0 1 5))) (.tip (.cover 0 1 4))) (.split 10 (.split 12 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.split 5 (.split 6 (.split 9 (.tip (.small 0)) (.tip (.unordered 5 0))) (.split 9 (.tip (.equal 4 7)) (.tip (.unordered 5 0)))) (.split 6 (.split 9 (.tip (.equal 3 4)) (.tip (.equal 2 7))) (.split 9 (.tip (.equal 3 5)) (.tip (.unordered 5 0)))))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 0)) (.tip (.unordered 4 0))) (.split 9 (.tip (.equal 3 4)) (.tip (.equal 2 7)))) (.split 6 (.split 9 (.tip (.equal 5 7)) (.tip (.unordered 4 0))) (.split 9 (.tip (.equal 3 4)) (.tip (.unordered 4 0))))) (.split 5 (.split 6 (.split 9 (.tip (.equal 3 7)) (.tip (.unordered 4 0))) (.tip (.cover 4 5 6))) (.tip (.cover 4 5 6))))) (.tip (.cover 0 3 7))) (.tip (.cover 0 1 5))) (.tip (.cover 0 1 4))))
private theorem q8Shape6T18OK : treeOK (forms 6) 10240 16664 q8Shape6T18=true := by decide

private def q8Shape6T19 : Tree := (.split 7 (.split 10 (.split 12 (.split 0 (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 0)) (.split 9 (.tip (.small 0)) (.tip (.unordered 5 0)))) (.split 6 (.split 9 (.tip (.small 0)) (.tip (.unordered 4 0))) (.split 9 (.tip (.equal 2 7)) (.tip (.unordered 4 0))))) (.split 5 (.split 6 (.tip (.equal 3 6)) (.split 9 (.tip (.equal 4 7)) (.tip (.unordered 5 0)))) (.split 6 (.split 9 (.tip (.equal 2 4)) (.tip (.equal 3 7))) (.tip (.cover 4 5 6))))) (.split 2 (.split 5 (.split 6 (.tip (.equal 3 6)) (.split 9 (.tip (.equal 2 4)) (.tip (.equal 3 7)))) (.split 6 (.split 9 (.tip (.equal 5 7)) (.tip (.unordered 4 0))) (.tip (.cover 4 5 6)))) (.split 5 (.split 6 (.tip (.equal 3 6)) (.split 9 (.tip (.equal 2 5)) (.tip (.unordered 5 0)))) (.split 6 (.split 9 (.tip (.equal 2 4)) (.tip (.unordered 4 0))) (.tip (.cover 4 5 6)))))) (.tip (.cover 0 2 7))) (.tip (.cover 0 1 5))) (.tip (.cover 0 1 4))) (.tip (.cover 0 6 7)))
private theorem q8Shape6T19OK : treeOK (forms 6) 10248 16656 q8Shape6T19=true := by decide

private def q8Shape6T17 : Tree := .split 3 q8Shape6T18 q8Shape6T19
private theorem q8Shape6T17OK : treeOK (forms 6) 10240 16656 q8Shape6T17=true := by
  change (treeOK (forms 6) 10240 (16656 ||| 2^3) q8Shape6T18 &&
    treeOK (forms 6) (10240 ||| 2^3) 16656 q8Shape6T19)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T18OK,q8Shape6T19OK⟩

private def q8Shape6T11 : Tree := .split 13 q8Shape6T12 q8Shape6T17
private theorem q8Shape6T11OK : treeOK (forms 6) 2048 16656 q8Shape6T11=true := by
  change (treeOK (forms 6) 2048 (16656 ||| 2^13) q8Shape6T12 &&
    treeOK (forms 6) (2048 ||| 2^13) 16656 q8Shape6T17)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T12OK,q8Shape6T17OK⟩

private def q8Shape6T3 : Tree := .split 11 q8Shape6T4 q8Shape6T11
private theorem q8Shape6T3OK : treeOK (forms 6) 0 16656 q8Shape6T3=true := by
  change (treeOK (forms 6) 0 (16656 ||| 2^11) q8Shape6T4 &&
    treeOK (forms 6) (0 ||| 2^11) 16656 q8Shape6T11)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T4OK,q8Shape6T11OK⟩

private def q8Shape6T23 : Tree := (.split 7 (.split 10 (.split 12 (.tip (.zero 6)) (.tip (.equal 6 7))) (.split 12 (.tip (.equal 6 7)) (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.unordered 5 1))) (.split 9 (.tip (.equal 4 6)) (.tip (.unordered 5 0)))) (.split 6 (.split 9 (.tip (.equal 3 4)) (.tip (.equal 2 6))) (.split 9 (.tip (.equal 3 5)) (.tip (.unordered 5 0)))))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.unordered 4 1))) (.split 9 (.tip (.equal 3 4)) (.tip (.equal 2 6)))) (.split 6 (.split 9 (.tip (.equal 5 6)) (.tip (.unordered 4 0))) (.split 9 (.tip (.equal 3 4)) (.tip (.unordered 4 0))))) (.split 5 (.split 6 (.split 9 (.tip (.equal 3 6)) (.tip (.unordered 4 1))) (.tip (.cover 4 5 7))) (.tip (.cover 4 5 7))))) (.tip (.cover 1 3 6))))) (.tip (.cover 0 1 3)))
private theorem q8Shape6T23OK : treeOK (forms 6) 256 26648 q8Shape6T23=true := by decide

private def q8Shape6T26 : Tree := (.split 12 (.tip (.equal 6 7)) (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.unordered 5 1))) (.split 9 (.tip (.unordered 5 1)) (.tip (.unordered 5 0)))) (.tip (.cover 1 3 6)))) (.split 2 (.split 5 (.split 6 (.tip (.equal 3 6)) (.tip (.equal 2 3))) (.tip (.cover 1 3 6))) (.tip (.cover 0 2 7)))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.equal 2 3)) (.split 9 (.tip (.equal 2 5)) (.tip (.equal 3 5)))) (.tip (.cover 1 3 6))) (.split 5 (.split 6 (.split 9 (.tip (.unordered 2 1)) (.tip (.equal 2 5))) (.split 9 (.tip (.unordered 2 1)) (.tip (.unordered 5 0)))) (.tip (.cover 1 3 6)))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.equal 5 6)) (.tip (.equal 3 5))) (.tip (.equal 2 3))) (.tip (.cover 1 3 6))) (.tip (.cover 0 2 7))))))
private theorem q8Shape6T26OK : treeOK (forms 6) 264 27792 q8Shape6T26=true := by decide

private def q8Shape6T27 : Tree := (.split 12 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.split 5 (.split 6 (.tip (.equal 3 6)) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.tip (.cover 1 3 6))))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 1)) (.tip (.unordered 4 1))) (.tip (.cover 1 3 6))) (.split 6 (.split 9 (.tip (.unordered 4 1)) (.tip (.unordered 4 0))) (.tip (.cover 1 3 6)))) (.tip (.cover 0 2 7)))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.equal 2 3)) (.tip (.cover 1 3 6))) (.split 6 (.split 9 (.tip (.equal 2 4)) (.tip (.equal 3 4))) (.tip (.cover 1 3 6)))) (.split 5 (.split 6 (.split 9 (.tip (.equal 4 6)) (.tip (.equal 3 4))) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.tip (.cover 1 3 6))))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.unordered 2 1)) (.tip (.equal 2 4))) (.tip (.cover 1 3 6))) (.split 6 (.split 9 (.tip (.unordered 2 1)) (.tip (.unordered 4 0))) (.tip (.cover 1 3 6)))) (.tip (.cover 0 2 7))))) (.tip (.cover 0 6 7)))
private theorem q8Shape6T27OK : treeOK (forms 6) 1288 26768 q8Shape6T27=true := by decide

private def q8Shape6T25 : Tree := .split 10 q8Shape6T26 q8Shape6T27
private theorem q8Shape6T25OK : treeOK (forms 6) 264 26768 q8Shape6T25=true := by
  change (treeOK (forms 6) 264 (26768 ||| 2^10) q8Shape6T26 &&
    treeOK (forms 6) (264 ||| 2^10) 26768 q8Shape6T27)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T26OK,q8Shape6T27OK⟩

private def q8Shape6T28 : Tree := (.tip (.cover 0 1 3))
private theorem q8Shape6T28OK : treeOK (forms 6) 392 26640 q8Shape6T28=true := by decide

private def q8Shape6T24 : Tree := .split 7 q8Shape6T25 q8Shape6T28
private theorem q8Shape6T24OK : treeOK (forms 6) 264 26640 q8Shape6T24=true := by
  change (treeOK (forms 6) 264 (26640 ||| 2^7) q8Shape6T25 &&
    treeOK (forms 6) (264 ||| 2^7) 26640 q8Shape6T28)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T25OK,q8Shape6T28OK⟩

private def q8Shape6T22 : Tree := .split 3 q8Shape6T23 q8Shape6T24
private theorem q8Shape6T22OK : treeOK (forms 6) 256 26640 q8Shape6T22=true := by
  change (treeOK (forms 6) 256 (26640 ||| 2^3) q8Shape6T23 &&
    treeOK (forms 6) (256 ||| 2^3) 26640 q8Shape6T24)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T23OK,q8Shape6T24OK⟩

private def q8Shape6T30 : Tree := (.split 7 (.split 10 (.split 12 (.tip (.zero 6)) (.tip (.cover 0 1 5))) (.split 12 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.split 5 (.split 6 (.tip (.equal 3 7)) (.tip (.equal 2 7))) (.split 6 (.split 9 (.tip (.equal 3 4)) (.tip (.equal 4 5))) (.tip (.equal 2 7))))) (.tip (.cover 0 4 7))) (.split 1 (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 0)) (.tip (.equal 3 4))) (.tip (.equal 2 7))) (.split 6 (.split 9 (.tip (.equal 5 7)) (.tip (.equal 3 4))) (.tip (.unordered 3 0)))) (.split 5 (.split 6 (.split 9 (.tip (.equal 3 5)) (.tip (.equal 3 4))) (.tip (.cover 1 3 6))) (.tip (.cover 3 5 6)))) (.tip (.cover 0 4 7)))) (.tip (.cover 0 1 5)))) (.tip (.cover 0 1 3)))
private theorem q8Shape6T30OK : treeOK (forms 6) 8448 18456 q8Shape6T30=true := by decide

private def q8Shape6T31 : Tree := (.split 7 (.split 10 (.split 12 (.split 0 (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 0)) (.split 9 (.tip (.small 0)) (.tip (.unordered 5 0)))) (.split 6 (.tip (.equal 2 7)) (.tip (.cover 1 3 6)))) (.split 5 (.split 6 (.tip (.equal 3 7)) (.split 9 (.tip (.unordered 5 0)) (.tip (.unordered 5 0)))) (.split 6 (.tip (.equal 2 3)) (.tip (.cover 1 3 6))))) (.tip (.cover 0 2 7))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.equal 2 3)) (.split 9 (.tip (.unordered 3 0)) (.tip (.equal 3 5)))) (.split 6 (.split 9 (.tip (.equal 5 7)) (.tip (.equal 2 5))) (.tip (.unordered 3 0)))) (.split 5 (.split 6 (.split 9 (.tip (.equal 3 5)) (.tip (.equal 2 5))) (.split 9 (.tip (.unordered 3 0)) (.tip (.unordered 5 0)))) (.split 6 (.tip (.equal 2 3)) (.tip (.unordered 3 0))))) (.tip (.cover 0 2 7)))) (.tip (.cover 0 1 5))) (.tip (.cover 0 6 7))) (.tip (.cover 0 1 3)))
private theorem q8Shape6T31OK : treeOK (forms 6) 8456 18448 q8Shape6T31=true := by decide

private def q8Shape6T29 : Tree := .split 3 q8Shape6T30 q8Shape6T31
private theorem q8Shape6T29OK : treeOK (forms 6) 8448 18448 q8Shape6T29=true := by
  change (treeOK (forms 6) 8448 (18448 ||| 2^3) q8Shape6T30 &&
    treeOK (forms 6) (8448 ||| 2^3) 18448 q8Shape6T31)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T30OK,q8Shape6T31OK⟩

private def q8Shape6T21 : Tree := .split 13 q8Shape6T22 q8Shape6T29
private theorem q8Shape6T21OK : treeOK (forms 6) 256 18448 q8Shape6T21=true := by
  change (treeOK (forms 6) 256 (18448 ||| 2^13) q8Shape6T22 &&
    treeOK (forms 6) (256 ||| 2^13) 18448 q8Shape6T29)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T22OK,q8Shape6T29OK⟩

private def q8Shape6T34 : Tree := (.split 7 (.split 10 (.split 12 (.tip (.zero 6)) (.split 0 (.split 1 (.split 2 (.tip (.equal 2 6)) (.tip (.cover 0 5 7))) (.split 2 (.split 5 (.split 6 (.tip (.equal 3 7)) (.split 9 (.tip (.equal 3 4)) (.tip (.equal 4 5)))) (.tip (.equal 2 7))) (.tip (.cover 0 5 7)))) (.split 1 (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 0)) (.tip (.equal 3 4))) (.split 9 (.tip (.equal 4 7)) (.tip (.equal 3 5)))) (.tip (.equal 2 7))) (.tip (.cover 0 5 7))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.equal 3 4)) (.tip (.equal 3 5))) (.tip (.cover 3 4 6))) (.tip (.cover 1 3 6))) (.tip (.cover 2 6 7)))))) (.tip (.cover 0 1 4))) (.tip (.cover 0 1 3)))
private theorem q8Shape6T34OK : treeOK (forms 6) 2304 24600 q8Shape6T34=true := by decide

private def q8Shape6T35 : Tree := (.split 7 (.split 10 (.split 12 (.split 0 (.split 1 (.split 2 (.split 5 (.tip (.equal 2 7)) (.split 6 (.split 9 (.tip (.small 0)) (.tip (.unordered 4 0))) (.tip (.cover 1 3 6)))) (.tip (.cover 0 2 7))) (.split 2 (.split 5 (.split 6 (.tip (.equal 3 7)) (.tip (.equal 2 3))) (.split 6 (.split 9 (.tip (.unordered 4 0)) (.tip (.unordered 4 0))) (.tip (.cover 1 3 6)))) (.tip (.cover 0 2 7)))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.equal 2 3)) (.split 9 (.tip (.equal 4 7)) (.tip (.equal 2 4)))) (.split 6 (.split 9 (.tip (.unordered 3 0)) (.tip (.equal 3 4))) (.tip (.unordered 3 0)))) (.tip (.cover 0 2 7))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.equal 3 4)) (.tip (.equal 2 4))) (.tip (.equal 2 3))) (.split 6 (.split 9 (.tip (.unordered 3 0)) (.tip (.unordered 4 0))) (.tip (.unordered 3 0)))) (.tip (.cover 0 2 7))))) (.tip (.cover 0 6 7))) (.tip (.cover 0 1 4))) (.tip (.cover 0 1 3)))
private theorem q8Shape6T35OK : treeOK (forms 6) 2312 24592 q8Shape6T35=true := by decide

private def q8Shape6T33 : Tree := .split 3 q8Shape6T34 q8Shape6T35
private theorem q8Shape6T33OK : treeOK (forms 6) 2304 24592 q8Shape6T33=true := by
  change (treeOK (forms 6) 2304 (24592 ||| 2^3) q8Shape6T34 &&
    treeOK (forms 6) (2304 ||| 2^3) 24592 q8Shape6T35)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T34OK,q8Shape6T35OK⟩

private def q8Shape6T36 : Tree := (.split 3 (.split 7 (.split 10 (.split 12 (.tip (.zero 6)) (.tip (.cover 0 1 5))) (.tip (.cover 0 1 4))) (.tip (.cover 0 1 3))) (.tip (.cover 0 2 7)))
private theorem q8Shape6T36OK : treeOK (forms 6) 10496 16400 q8Shape6T36=true := by decide

private def q8Shape6T32 : Tree := .split 13 q8Shape6T33 q8Shape6T36
private theorem q8Shape6T32OK : treeOK (forms 6) 2304 16400 q8Shape6T32=true := by
  change (treeOK (forms 6) 2304 (16400 ||| 2^13) q8Shape6T33 &&
    treeOK (forms 6) (2304 ||| 2^13) 16400 q8Shape6T36)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T33OK,q8Shape6T36OK⟩

private def q8Shape6T20 : Tree := .split 11 q8Shape6T21 q8Shape6T32
private theorem q8Shape6T20OK : treeOK (forms 6) 256 16400 q8Shape6T20=true := by
  change (treeOK (forms 6) 256 (16400 ||| 2^11) q8Shape6T21 &&
    treeOK (forms 6) (256 ||| 2^11) 16400 q8Shape6T32)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T21OK,q8Shape6T32OK⟩

private def q8Shape6T2 : Tree := .split 8 q8Shape6T3 q8Shape6T20
private theorem q8Shape6T2OK : treeOK (forms 6) 0 16400 q8Shape6T2=true := by
  change (treeOK (forms 6) 0 (16400 ||| 2^8) q8Shape6T3 &&
    treeOK (forms 6) (0 ||| 2^8) 16400 q8Shape6T20)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T3OK,q8Shape6T20OK⟩

private def q8Shape6T42 : Tree := (.split 10 (.split 12 (.tip (.zero 6)) (.tip (.equal 6 7))) (.split 12 (.tip (.equal 6 7)) (.split 0 (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.unordered 5 1)))) (.split 6 (.split 9 (.tip (.small 1)) (.tip (.unordered 4 1))) (.split 9 (.tip (.equal 2 6)) (.tip (.unordered 4 1))))) (.split 5 (.split 6 (.tip (.equal 3 7)) (.split 9 (.tip (.equal 4 6)) (.tip (.unordered 5 0)))) (.split 6 (.split 9 (.tip (.equal 2 4)) (.tip (.equal 3 6))) (.tip (.cover 4 5 7))))) (.split 2 (.split 5 (.split 6 (.tip (.equal 3 7)) (.split 9 (.tip (.equal 2 4)) (.tip (.equal 3 6)))) (.split 6 (.split 9 (.tip (.equal 5 6)) (.tip (.unordered 4 0))) (.tip (.cover 4 5 7)))) (.split 5 (.split 6 (.tip (.equal 3 7)) (.split 9 (.tip (.equal 2 5)) (.tip (.unordered 5 0)))) (.split 6 (.split 9 (.tip (.equal 2 4)) (.tip (.unordered 4 0))) (.tip (.cover 4 5 7)))))) (.tip (.cover 1 2 6)))))
private theorem q8Shape6T42OK : treeOK (forms 6) 16 27016 q8Shape6T42=true := by decide

private def q8Shape6T44 : Tree := (.split 12 (.tip (.equal 6 7)) (.split 0 (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.unordered 5 1)))) (.split 6 (.tip (.equal 2 6)) (.tip (.cover 0 3 7)))) (.split 5 (.split 6 (.tip (.equal 3 6)) (.split 9 (.tip (.unordered 5 1)) (.tip (.unordered 5 0)))) (.split 6 (.tip (.equal 2 3)) (.tip (.cover 0 3 7))))) (.tip (.cover 1 2 6))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.equal 2 3)) (.split 9 (.tip (.unordered 3 1)) (.tip (.equal 3 5)))) (.split 6 (.split 9 (.tip (.equal 5 6)) (.tip (.equal 2 5))) (.tip (.unordered 3 1)))) (.split 5 (.split 6 (.split 9 (.tip (.equal 3 5)) (.tip (.equal 2 5))) (.split 9 (.tip (.unordered 3 1)) (.tip (.unordered 5 0)))) (.split 6 (.tip (.equal 2 3)) (.tip (.unordered 3 1))))) (.tip (.cover 1 2 6)))))
private theorem q8Shape6T44OK : treeOK (forms 6) 144 27912 q8Shape6T44=true := by decide

private def q8Shape6T45 : Tree := (.split 12 (.split 0 (.split 1 (.split 2 (.split 5 (.tip (.equal 2 6)) (.split 6 (.split 9 (.tip (.small 1)) (.tip (.unordered 4 1))) (.tip (.cover 0 3 7)))) (.tip (.cover 1 2 6))) (.split 2 (.split 5 (.split 6 (.tip (.equal 3 6)) (.tip (.equal 2 3))) (.split 6 (.split 9 (.tip (.unordered 4 1)) (.tip (.unordered 4 0))) (.tip (.cover 0 3 7)))) (.tip (.cover 1 2 6)))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.equal 2 3)) (.split 9 (.tip (.equal 4 6)) (.tip (.equal 2 4)))) (.split 6 (.split 9 (.tip (.unordered 3 1)) (.tip (.equal 3 4))) (.tip (.unordered 3 1)))) (.tip (.cover 1 2 6))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.equal 3 4)) (.tip (.equal 2 4))) (.tip (.equal 2 3))) (.split 6 (.split 9 (.tip (.unordered 3 1)) (.tip (.unordered 4 0))) (.tip (.unordered 3 1)))) (.tip (.cover 1 2 6))))) (.tip (.cover 0 6 7)))
private theorem q8Shape6T45OK : treeOK (forms 6) 1168 26888 q8Shape6T45=true := by decide

private def q8Shape6T43 : Tree := .split 10 q8Shape6T44 q8Shape6T45
private theorem q8Shape6T43OK : treeOK (forms 6) 144 26888 q8Shape6T43=true := by
  change (treeOK (forms 6) 144 (26888 ||| 2^10) q8Shape6T44 &&
    treeOK (forms 6) (144 ||| 2^10) 26888 q8Shape6T45)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T44OK,q8Shape6T45OK⟩

private def q8Shape6T41 : Tree := .split 7 q8Shape6T42 q8Shape6T43
private theorem q8Shape6T41OK : treeOK (forms 6) 16 26888 q8Shape6T41=true := by
  change (treeOK (forms 6) 16 (26888 ||| 2^7) q8Shape6T42 &&
    treeOK (forms 6) (16 ||| 2^7) 26888 q8Shape6T43)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T42OK,q8Shape6T43OK⟩

private def q8Shape6T46 : Tree := (.tip (.cover 0 1 2))
private theorem q8Shape6T46OK : treeOK (forms 6) 24 26880 q8Shape6T46=true := by decide

private def q8Shape6T40 : Tree := .split 3 q8Shape6T41 q8Shape6T46
private theorem q8Shape6T40OK : treeOK (forms 6) 16 26880 q8Shape6T40=true := by
  change (treeOK (forms 6) 16 (26880 ||| 2^3) q8Shape6T41 &&
    treeOK (forms 6) (16 ||| 2^3) 26880 q8Shape6T46)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T41OK,q8Shape6T46OK⟩

private def q8Shape6T49 : Tree := (.split 10 (.split 12 (.tip (.zero 6)) (.tip (.cover 0 1 5))) (.split 12 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.split 5 (.split 6 (.tip (.equal 3 6)) (.tip (.equal 3 7))) (.tip (.cover 0 4 7)))) (.split 2 (.split 5 (.split 6 (.tip (.equal 3 6)) (.split 9 (.tip (.equal 2 4)) (.tip (.equal 4 5)))) (.tip (.cover 0 4 7))) (.split 5 (.split 6 (.tip (.equal 3 6)) (.tip (.equal 3 7))) (.tip (.cover 0 4 7))))) (.split 1 (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 0)) (.tip (.equal 2 4))) (.split 9 (.tip (.equal 2 5)) (.tip (.equal 2 4)))) (.tip (.cover 0 4 7))) (.tip (.cover 1 2 6))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.equal 5 7)) (.tip (.equal 2 4))) (.tip (.cover 2 5 6))) (.tip (.cover 0 4 7))) (.tip (.cover 1 2 6))))) (.tip (.cover 0 1 5))))
private theorem q8Shape6T49OK : treeOK (forms 6) 8208 18824 q8Shape6T49=true := by decide

private def q8Shape6T50 : Tree := (.split 10 (.split 12 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.split 5 (.split 6 (.split 9 (.tip (.small 0)) (.tip (.unordered 5 0))) (.split 9 (.tip (.unordered 5 0)) (.tip (.unordered 5 0)))) (.tip (.cover 0 3 7)))) (.split 2 (.split 5 (.split 6 (.tip (.equal 3 7)) (.tip (.equal 2 3))) (.tip (.cover 0 3 7))) (.tip (.cover 1 2 6)))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.equal 2 3)) (.split 9 (.tip (.equal 2 5)) (.tip (.equal 3 5)))) (.tip (.cover 0 3 7))) (.split 5 (.split 6 (.split 9 (.tip (.unordered 2 0)) (.tip (.equal 2 5))) (.split 9 (.tip (.unordered 2 0)) (.tip (.unordered 5 0)))) (.tip (.cover 0 3 7)))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.equal 5 7)) (.tip (.equal 3 5))) (.tip (.equal 2 3))) (.tip (.cover 0 3 7))) (.tip (.cover 1 2 6))))) (.tip (.cover 0 1 5))) (.tip (.cover 0 6 7)))
private theorem q8Shape6T50OK : treeOK (forms 6) 8336 18696 q8Shape6T50=true := by decide

private def q8Shape6T48 : Tree := .split 7 q8Shape6T49 q8Shape6T50
private theorem q8Shape6T48OK : treeOK (forms 6) 8208 18696 q8Shape6T48=true := by
  change (treeOK (forms 6) 8208 (18696 ||| 2^7) q8Shape6T49 &&
    treeOK (forms 6) (8208 ||| 2^7) 18696 q8Shape6T50)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T49OK,q8Shape6T50OK⟩

private def q8Shape6T51 : Tree := (.tip (.cover 0 1 2))
private theorem q8Shape6T51OK : treeOK (forms 6) 8216 18688 q8Shape6T51=true := by decide

private def q8Shape6T47 : Tree := .split 3 q8Shape6T48 q8Shape6T51
private theorem q8Shape6T47OK : treeOK (forms 6) 8208 18688 q8Shape6T47=true := by
  change (treeOK (forms 6) 8208 (18688 ||| 2^3) q8Shape6T48 &&
    treeOK (forms 6) (8208 ||| 2^3) 18688 q8Shape6T51)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T48OK,q8Shape6T51OK⟩

private def q8Shape6T39 : Tree := .split 13 q8Shape6T40 q8Shape6T47
private theorem q8Shape6T39OK : treeOK (forms 6) 16 18688 q8Shape6T39=true := by
  change (treeOK (forms 6) 16 (18688 ||| 2^13) q8Shape6T40 &&
    treeOK (forms 6) (16 ||| 2^13) 18688 q8Shape6T47)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T40OK,q8Shape6T47OK⟩

private def q8Shape6T55 : Tree := (.split 10 (.split 12 (.tip (.zero 6)) (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.split 5 (.split 6 (.tip (.equal 3 6)) (.tip (.cover 0 5 7))) (.split 6 (.split 9 (.tip (.equal 2 4)) (.tip (.equal 4 5))) (.tip (.cover 0 5 7))))) (.split 2 (.split 5 (.split 6 (.tip (.equal 3 6)) (.tip (.equal 3 7))) (.tip (.cover 1 4 6))) (.split 5 (.split 6 (.tip (.equal 3 6)) (.tip (.equal 3 7))) (.tip (.cover 1 4 6))))) (.split 1 (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 0)) (.tip (.equal 2 4))) (.tip (.cover 0 5 7))) (.split 6 (.split 9 (.tip (.equal 2 4)) (.tip (.equal 2 5))) (.tip (.cover 3 6 7)))) (.split 5 (.split 6 (.split 9 (.tip (.equal 4 7)) (.tip (.equal 2 5))) (.tip (.cover 0 5 7))) (.tip (.cover 2 4 6)))) (.tip (.cover 1 2 6))))) (.tip (.cover 0 1 4)))
private theorem q8Shape6T55OK : treeOK (forms 6) 2064 24968 q8Shape6T55=true := by decide

private def q8Shape6T56 : Tree := (.split 10 (.split 12 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.split 5 (.split 6 (.tip (.equal 3 7)) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.tip (.cover 0 3 7))))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.small 0)) (.tip (.unordered 4 0))) (.tip (.cover 0 3 7))) (.split 6 (.split 9 (.tip (.unordered 4 0)) (.tip (.unordered 4 0))) (.tip (.cover 0 3 7)))) (.tip (.cover 1 2 6)))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.equal 2 3)) (.tip (.cover 0 3 7))) (.split 6 (.split 9 (.tip (.equal 2 4)) (.tip (.equal 3 4))) (.tip (.cover 0 3 7)))) (.split 5 (.split 6 (.split 9 (.tip (.equal 4 7)) (.tip (.equal 3 4))) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.tip (.cover 0 3 7))))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.unordered 2 0)) (.tip (.equal 2 4))) (.tip (.cover 0 3 7))) (.split 6 (.split 9 (.tip (.unordered 2 0)) (.tip (.unordered 4 0))) (.tip (.cover 0 3 7)))) (.tip (.cover 1 2 6))))) (.tip (.cover 0 6 7))) (.tip (.cover 0 1 4)))
private theorem q8Shape6T56OK : treeOK (forms 6) 2192 24840 q8Shape6T56=true := by decide

private def q8Shape6T54 : Tree := .split 7 q8Shape6T55 q8Shape6T56
private theorem q8Shape6T54OK : treeOK (forms 6) 2064 24840 q8Shape6T54=true := by
  change (treeOK (forms 6) 2064 (24840 ||| 2^7) q8Shape6T55 &&
    treeOK (forms 6) (2064 ||| 2^7) 24840 q8Shape6T56)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T55OK,q8Shape6T56OK⟩

private def q8Shape6T57 : Tree := (.tip (.cover 0 1 2))
private theorem q8Shape6T57OK : treeOK (forms 6) 2072 24832 q8Shape6T57=true := by decide

private def q8Shape6T53 : Tree := .split 3 q8Shape6T54 q8Shape6T57
private theorem q8Shape6T53OK : treeOK (forms 6) 2064 24832 q8Shape6T53=true := by
  change (treeOK (forms 6) 2064 (24832 ||| 2^3) q8Shape6T54 &&
    treeOK (forms 6) (2064 ||| 2^3) 24832 q8Shape6T57)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T54OK,q8Shape6T57OK⟩

private def q8Shape6T58 : Tree := (.split 3 (.split 7 (.split 10 (.split 12 (.tip (.zero 6)) (.tip (.cover 0 1 5))) (.tip (.cover 0 1 4))) (.tip (.cover 0 3 7))) (.tip (.cover 0 1 2)))
private theorem q8Shape6T58OK : treeOK (forms 6) 10256 16640 q8Shape6T58=true := by decide

private def q8Shape6T52 : Tree := .split 13 q8Shape6T53 q8Shape6T58
private theorem q8Shape6T52OK : treeOK (forms 6) 2064 16640 q8Shape6T52=true := by
  change (treeOK (forms 6) 2064 (16640 ||| 2^13) q8Shape6T53 &&
    treeOK (forms 6) (2064 ||| 2^13) 16640 q8Shape6T58)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T53OK,q8Shape6T58OK⟩

private def q8Shape6T38 : Tree := .split 11 q8Shape6T39 q8Shape6T52
private theorem q8Shape6T38OK : treeOK (forms 6) 16 16640 q8Shape6T38=true := by
  change (treeOK (forms 6) 16 (16640 ||| 2^11) q8Shape6T39 &&
    treeOK (forms 6) (16 ||| 2^11) 16640 q8Shape6T52)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T39OK,q8Shape6T52OK⟩

private def q8Shape6T64 : Tree := (.split 12 (.tip (.zero 6)) (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.split 5 (.split 6 (.tip (.equal 3 7)) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.split 9 (.tip (.equal 3 5)) (.tip (.unordered 5 0)))))) (.split 2 (.split 5 (.split 6 (.tip (.equal 3 7)) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.tip (.cover 2 3 6)))) (.split 5 (.split 6 (.tip (.equal 3 7)) (.split 9 (.tip (.equal 2 5)) (.tip (.unordered 5 0)))) (.tip (.cover 2 3 6))))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.equal 2 3)) (.split 9 (.tip (.unordered 3 0)) (.tip (.equal 4 7)))) (.tip (.cover 1 3 6))) (.split 5 (.split 6 (.split 9 (.tip (.unordered 2 0)) (.tip (.equal 4 7))) (.tip (.equal 2 3))) (.tip (.cover 1 3 6)))) (.tip (.cover 1 2 6)))))
private theorem q8Shape6T64OK : treeOK (forms 6) 272 27784 q8Shape6T64=true := by decide

private def q8Shape6T65 : Tree := (.split 12 (.split 0 (.split 1 (.split 2 (.tip (.equal 2 7)) (.split 5 (.split 6 (.tip (.equal 3 7)) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.tip (.cover 2 3 6))))) (.split 2 (.split 5 (.split 6 (.tip (.equal 3 7)) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.split 9 (.tip (.equal 3 4)) (.tip (.unordered 4 0))))) (.split 5 (.split 6 (.tip (.equal 3 7)) (.tip (.cover 2 3 6))) (.split 6 (.split 9 (.tip (.equal 2 4)) (.tip (.unordered 4 0))) (.tip (.cover 2 3 6)))))) (.split 1 (.split 2 (.split 5 (.split 6 (.tip (.equal 2 3)) (.tip (.cover 1 3 6))) (.split 6 (.split 9 (.tip (.unordered 3 0)) (.tip (.equal 5 7))) (.tip (.unordered 3 0)))) (.tip (.cover 1 2 6))) (.split 2 (.split 5 (.split 6 (.split 9 (.tip (.unordered 2 0)) (.tip (.equal 5 7))) (.tip (.equal 2 3))) (.split 6 (.tip (.equal 2 3)) (.tip (.unordered 3 0)))) (.tip (.cover 1 2 6))))) (.tip (.cover 0 6 7)))
private theorem q8Shape6T65OK : treeOK (forms 6) 1296 26760 q8Shape6T65=true := by decide

private def q8Shape6T63 : Tree := .split 10 q8Shape6T64 q8Shape6T65
private theorem q8Shape6T63OK : treeOK (forms 6) 272 26760 q8Shape6T63=true := by
  change (treeOK (forms 6) 272 (26760 ||| 2^10) q8Shape6T64 &&
    treeOK (forms 6) (272 ||| 2^10) 26760 q8Shape6T65)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T64OK,q8Shape6T65OK⟩

private def q8Shape6T66 : Tree := (.tip (.cover 0 1 3))
private theorem q8Shape6T66OK : treeOK (forms 6) 400 26632 q8Shape6T66=true := by decide

private def q8Shape6T62 : Tree := .split 7 q8Shape6T63 q8Shape6T66
private theorem q8Shape6T62OK : treeOK (forms 6) 272 26632 q8Shape6T62=true := by
  change (treeOK (forms 6) 272 (26632 ||| 2^7) q8Shape6T63 &&
    treeOK (forms 6) (272 ||| 2^7) 26632 q8Shape6T66)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T63OK,q8Shape6T66OK⟩

private def q8Shape6T67 : Tree := (.tip (.cover 0 1 2))
private theorem q8Shape6T67OK : treeOK (forms 6) 280 26624 q8Shape6T67=true := by decide

private def q8Shape6T61 : Tree := .split 3 q8Shape6T62 q8Shape6T67
private theorem q8Shape6T61OK : treeOK (forms 6) 272 26624 q8Shape6T61=true := by
  change (treeOK (forms 6) 272 (26624 ||| 2^3) q8Shape6T62 &&
    treeOK (forms 6) (272 ||| 2^3) 26624 q8Shape6T67)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T62OK,q8Shape6T67OK⟩

private def q8Shape6T68 : Tree := (.split 3 (.split 7 (.split 10 (.split 12 (.tip (.zero 6)) (.tip (.cover 0 1 5))) (.tip (.cover 0 4 7))) (.tip (.cover 0 1 3))) (.tip (.cover 0 1 2)))
private theorem q8Shape6T68OK : treeOK (forms 6) 8464 18432 q8Shape6T68=true := by decide

private def q8Shape6T60 : Tree := .split 13 q8Shape6T61 q8Shape6T68
private theorem q8Shape6T60OK : treeOK (forms 6) 272 18432 q8Shape6T60=true := by
  change (treeOK (forms 6) 272 (18432 ||| 2^13) q8Shape6T61 &&
    treeOK (forms 6) (272 ||| 2^13) 18432 q8Shape6T68)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T61OK,q8Shape6T68OK⟩

private def q8Shape6T69 : Tree := (.split 13 (.split 3 (.split 7 (.split 10 (.split 12 (.tip (.zero 6)) (.tip (.cover 0 5 7))) (.tip (.cover 0 1 4))) (.tip (.cover 0 1 3))) (.tip (.cover 0 1 2))) (.tip (.cover 0 6 7)))
private theorem q8Shape6T69OK : treeOK (forms 6) 2320 16384 q8Shape6T69=true := by decide

private def q8Shape6T59 : Tree := .split 11 q8Shape6T60 q8Shape6T69
private theorem q8Shape6T59OK : treeOK (forms 6) 272 16384 q8Shape6T59=true := by
  change (treeOK (forms 6) 272 (16384 ||| 2^11) q8Shape6T60 &&
    treeOK (forms 6) (272 ||| 2^11) 16384 q8Shape6T69)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T60OK,q8Shape6T69OK⟩

private def q8Shape6T37 : Tree := .split 8 q8Shape6T38 q8Shape6T59
private theorem q8Shape6T37OK : treeOK (forms 6) 16 16384 q8Shape6T37=true := by
  change (treeOK (forms 6) 16 (16384 ||| 2^8) q8Shape6T38 &&
    treeOK (forms 6) (16 ||| 2^8) 16384 q8Shape6T59)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T38OK,q8Shape6T59OK⟩

private def q8Shape6T1 : Tree := .split 4 q8Shape6T2 q8Shape6T37
private theorem q8Shape6T1OK : treeOK (forms 6) 0 16384 q8Shape6T1=true := by
  change (treeOK (forms 6) 0 (16384 ||| 2^4) q8Shape6T2 &&
    treeOK (forms 6) (0 ||| 2^4) 16384 q8Shape6T37)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T2OK,q8Shape6T37OK⟩

private def q8Shape6T70 : Tree := (.tip (.cover 0 1 6))
private theorem q8Shape6T70OK : treeOK (forms 6) 16384 0 q8Shape6T70=true := by decide

private def q8Shape6T0 : Tree := .split 14 q8Shape6T1 q8Shape6T70
private theorem q8Shape6T0OK : treeOK (forms 6) 0 0 q8Shape6T0=true := by
  change (treeOK (forms 6) 0 (0 ||| 2^14) q8Shape6T1 &&
    treeOK (forms 6) (0 ||| 2^14) 0 q8Shape6T70)=true
  rw [Bool.and_eq_true]
  exact ⟨q8Shape6T1OK,q8Shape6T70OK⟩


theorem q8Shape6_cover (b : Nat→Bool) (H : Ranked (adj (forms 6) b)) :
    ∃ u v w,Dominates3 (adj (forms 6) b) u v w :=
  checked_tree (forms 6) b H q8Shape6T0 q8Shape6T0OK

#print axioms q8Shape6_cover
end Graffiti384b.Q8
