import SmallPalette384b
import Mathlib.Tactic.FinCases
namespace Graffiti384b.SmallPalette
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 500000

private def shape8_0 : Shape := ⟨false,4,4,2⟩
private def t8_1 : Tree 8 := (.split 9 (.tip (.small 0)) (.split 14 (.tip (.small 1)) (.tip (.cover 2 3 4 6))))
private theorem t8_1OK : treeOK shape8_0 0 1 t8_1=true := by decide

private def t8_3 : Tree 8 := (.split 6 (.tip (.small 0)) (.split 7 (.split 2 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.split 8 (.tip (.small 1)) (.tip (.cover 0 1 2 3))))) (.split 8 (.split 2 (.tip (.small 0)) (.split 3 (.tip (.small 1)) (.tip (.cover 0 1 2 3)))) (.tip (.cover 0 2 6 7)))))
private theorem t8_3OK : treeOK shape8_0 1 2 t8_3=true := by decide

private def t8_4 : Tree 8 := (.split 2 (.split 5 (.tip (.small 0)) (.split 7 (.split 4 (.tip (.small 1)) (.split 8 (.tip (.small 1)) (.tip (.cover 0 1 2 3)))) (.split 8 (.split 3 (.tip (.small 1)) (.tip (.cover 0 1 2 3))) (.tip (.cover 0 2 6 7))))) (.tip (.cover 1 3 4 5)))
private theorem t8_4OK : treeOK shape8_0 3 0 t8_4=true := by decide

private def t8_2 : Tree 8 := .split 1 t8_3 t8_4
private theorem t8_2OK : treeOK shape8_0 1 0 t8_2=true := by
  change (treeOK shape8_0 1 (0 ||| 2^1) t8_3 && treeOK shape8_0 (1 ||| 2^1) 0 t8_4)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_3OK,t8_4OK⟩

private def t8_0 : Tree 8 := .split 0 t8_1 t8_2
private theorem t8_0OK : treeOK shape8_0 0 0 t8_0=true := by
  change (treeOK shape8_0 0 (0 ||| 2^0) t8_1 && treeOK shape8_0 (0 ||| 2^0) 0 t8_2)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_1OK,t8_2OK⟩

private def shape8_1 : Shape := ⟨false,4,4,3⟩
private def t8_6 : Tree 8 := (.split 1 (.tip (.small 0)) (.split 5 (.tip (.small 0)) (.split 9 (.tip (.small 0)) (.tip (.cover 1 2 3 5)))))
private theorem t8_6OK : treeOK shape8_1 0 1 t8_6=true := by decide

private def t8_7 : Tree 8 := (.split 1 (.split 5 (.tip (.small 0)) (.split 6 (.tip (.small 0)) (.tip (.cover 1 2 4 5)))) (.split 5 (.split 2 (.tip (.small 0)) (.tip (.cover 1 3 4 5))) (.split 2 (.split 7 (.split 9 (.tip (.small 0)) (.tip (.cover 1 2 3 5))) (.tip (.cover 0 2 4 6))) (.tip (.cover 1 3 4 5)))))
private theorem t8_7OK : treeOK shape8_1 1 0 t8_7=true := by decide

private def t8_5 : Tree 8 := .split 0 t8_6 t8_7
private theorem t8_5OK : treeOK shape8_1 0 0 t8_5=true := by
  change (treeOK shape8_1 0 (0 ||| 2^0) t8_6 && treeOK shape8_1 (0 ||| 2^0) 0 t8_7)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_6OK,t8_7OK⟩

private def shape8_2 : Shape := ⟨false,5,4,3⟩
private def t8_9 : Tree 8 := (.split 1 (.tip (.small 1)) (.split 5 (.tip (.small 1)) (.split 9 (.split 3 (.split 7 (.tip (.cover 1 2 3 6)) (.split 8 (.tip (.small 1)) (.tip (.cover 2 4 6 7)))) (.split 4 (.tip (.small 1)) (.tip (.cover 3 4 6 7)))) (.tip (.cover 1 2 3 5)))))
private theorem t8_9OK : treeOK shape8_2 0 1 t8_9=true := by decide

private def t8_11 : Tree 8 := (.split 5 (.tip (.small 1)) (.split 6 (.split 3 (.split 8 (.tip (.small 1)) (.tip (.cover 0 2 4 7))) (.split 4 (.tip (.small 1)) (.tip (.cover 3 4 6 7)))) (.tip (.cover 1 2 4 5))))
private theorem t8_11OK : treeOK shape8_2 1 2 t8_11=true := by decide

private def t8_13 : Tree 8 := (.split 2 (.split 3 (.split 8 (.tip (.small 1)) (.split 11 (.tip (.small 1)) (.tip (.cover 0 1 2 7)))) (.tip (.cover 1 3 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t8_13OK : treeOK shape8_2 3 32 t8_13=true := by decide

private def t8_14 : Tree 8 := (.split 2 (.split 7 (.split 11 (.split 3 (.tip (.cover 1 2 3 6)) (.tip (.cover 1 3 4 6))) (.tip (.cover 0 2 3 7))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t8_14OK : treeOK shape8_2 35 0 t8_14=true := by decide

private def t8_12 : Tree 8 := .split 5 t8_13 t8_14
private theorem t8_12OK : treeOK shape8_2 3 0 t8_12=true := by
  change (treeOK shape8_2 3 (0 ||| 2^5) t8_13 && treeOK shape8_2 (3 ||| 2^5) 0 t8_14)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_13OK,t8_14OK⟩

private def t8_10 : Tree 8 := .split 1 t8_11 t8_12
private theorem t8_10OK : treeOK shape8_2 1 0 t8_10=true := by
  change (treeOK shape8_2 1 (0 ||| 2^1) t8_11 && treeOK shape8_2 (1 ||| 2^1) 0 t8_12)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_11OK,t8_12OK⟩

private def t8_8 : Tree 8 := .split 0 t8_9 t8_10
private theorem t8_8OK : treeOK shape8_2 0 0 t8_8=true := by
  change (treeOK shape8_2 0 (0 ||| 2^0) t8_9 && treeOK shape8_2 (0 ||| 2^0) 0 t8_10)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_9OK,t8_10OK⟩

private def shape8_3 : Shape := ⟨true,4,4,0⟩
private def t8_15 : Tree 8 := (.tip (.small 0))
private theorem t8_15OK : treeOK shape8_3 0 0 t8_15=true := by decide

private def shape8_4 : Shape := ⟨true,4,4,1⟩
private def t8_16 : Tree 8 := (.tip (.small 0))
private theorem t8_16OK : treeOK shape8_4 0 0 t8_16=true := by decide

private def shape8_5 : Shape := ⟨true,5,4,1⟩
private def t8_17 : Tree 8 := (.tip (.small 1))
private theorem t8_17OK : treeOK shape8_5 0 0 t8_17=true := by decide

private def shape8_6 : Shape := ⟨true,4,4,2⟩
private def t8_18 : Tree 8 := (.split 0 (.tip (.small 0)) (.split 1 (.tip (.small 0)) (.split 2 (.tip (.small 1)) (.split 5 (.tip (.small 0)) (.split 6 (.tip (.small 1)) (.tip (.cover 0 1 4 5)))))))
private theorem t8_18OK : treeOK shape8_6 0 0 t8_18=true := by decide

private def shape8_7 : Shape := ⟨true,5,4,2⟩
private def t8_20 : Tree 8 := (.tip (.small 1))
private theorem t8_20OK : treeOK shape8_7 0 1 t8_20=true := by decide

private def t8_23 : Tree 8 := (.split 3 (.tip (.small 1)) (.split 7 (.tip (.small 1)) (.split 14 (.tip (.cover 0 1 6 7)) (.split 2 (.tip (.cover 1 2 3 5)) (.tip (.cover 1 3 5 6))))))
private theorem t8_23OK : treeOK shape8_7 1 66 t8_23=true := by decide

private def t8_24 : Tree 8 := (.split 7 (.tip (.small 1)) (.split 2 (.split 5 (.split 14 (.split 9 (.tip (.small 0)) (.tip (.cover 0 2 5 6))) (.tip (.cover 1 2 5 6))) (.tip (.cover 1 2 4 5))) (.split 3 (.tip (.small 1)) (.tip (.cover 0 1 5 6)))))
private theorem t8_24OK : treeOK shape8_7 65 2 t8_24=true := by decide

private def t8_22 : Tree 8 := .split 6 t8_23 t8_24
private theorem t8_22OK : treeOK shape8_7 1 2 t8_22=true := by
  change (treeOK shape8_7 1 (2 ||| 2^6) t8_23 && treeOK shape8_7 (1 ||| 2^6) 2 t8_24)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_23OK,t8_24OK⟩

private def t8_25 : Tree 8 := (.split 2 (.split 5 (.split 3 (.tip (.small 1)) (.split 7 (.tip (.small 1)) (.split 14 (.tip (.cover 0 1 6 7)) (.tip (.cover 1 3 4 6))))) (.split 7 (.tip (.small 1)) (.split 3 (.tip (.small 1)) (.tip (.cover 0 1 4 6))))) (.tip (.cover 1 3 4 5)))
private theorem t8_25OK : treeOK shape8_7 3 0 t8_25=true := by decide

private def t8_21 : Tree 8 := .split 1 t8_22 t8_25
private theorem t8_21OK : treeOK shape8_7 1 0 t8_21=true := by
  change (treeOK shape8_7 1 (0 ||| 2^1) t8_22 && treeOK shape8_7 (1 ||| 2^1) 0 t8_25)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_22OK,t8_25OK⟩

private def t8_19 : Tree 8 := .split 0 t8_20 t8_21
private theorem t8_19OK : treeOK shape8_7 0 0 t8_19=true := by
  change (treeOK shape8_7 0 (0 ||| 2^0) t8_20 && treeOK shape8_7 (0 ||| 2^0) 0 t8_21)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_20OK,t8_21OK⟩

private def shape8_8 : Shape := ⟨true,5,5,2⟩
private def t8_30 : Tree 8 := (.split 2 (.tip (.small 0)) (.split 5 (.tip (.small 0)) (.split 6 (.tip (.small 0)) (.split 7 (.split 8 (.tip (.small 1)) (.tip (.cover 2 4 5 7))) (.tip (.cover 2 4 5 6))))))
private theorem t8_30OK : treeOK shape8_8 0 16899 t8_30=true := by decide

private def t8_31 : Tree 8 := (.split 2 (.split 5 (.tip (.small 0)) (.split 6 (.tip (.small 0)) (.split 7 (.split 8 (.tip (.small 1)) (.tip (.cover 2 4 5 7))) (.tip (.cover 2 4 5 6))))) (.split 3 (.split 4 (.tip (.small 1)) (.tip (.cover 3 4 5 7))) (.tip (.cover 3 4 5 6))))
private theorem t8_31OK : treeOK shape8_8 2 16897 t8_31=true := by decide

private def t8_29 : Tree 8 := .split 1 t8_30 t8_31
private theorem t8_29OK : treeOK shape8_8 0 16897 t8_29=true := by
  change (treeOK shape8_8 0 (16897 ||| 2^1) t8_30 && treeOK shape8_8 (0 ||| 2^1) 16897 t8_31)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_30OK,t8_31OK⟩

private def t8_34 : Tree 8 := (.split 4 (.tip (.small 1)) (.split 8 (.tip (.small 1)) (.tip (.cover 0 2 3 6))))
private theorem t8_34OK : treeOK shape8_8 16384 649 t8_34=true := by decide

private def t8_35 : Tree 8 := (.split 8 (.split 4 (.tip (.small 1)) (.split 1 (.split 2 (.tip (.small 0)) (.tip (.cover 0 1 2 6))) (.tip (.cover 0 1 2 6)))) (.split 4 (.split 5 (.split 6 (.tip (.small 0)) (.tip (.cover 2 5 6 7))) (.tip (.cover 2 4 6 7))) (.tip (.cover 0 2 3 6))))
private theorem t8_35OK : treeOK shape8_8 16512 521 t8_35=true := by decide

private def t8_33 : Tree 8 := .split 7 t8_34 t8_35
private theorem t8_33OK : treeOK shape8_8 16384 521 t8_33=true := by
  change (treeOK shape8_8 16384 (521 ||| 2^7) t8_34 && treeOK shape8_8 (16384 ||| 2^7) 521 t8_35)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_34OK,t8_35OK⟩

private def t8_36 : Tree 8 := (.split 4 (.split 7 (.split 8 (.tip (.small 1)) (.split 1 (.split 2 (.tip (.small 0)) (.tip (.cover 0 1 2 7))) (.tip (.cover 0 1 2 7)))) (.tip (.cover 0 2 3 7))) (.split 7 (.split 1 (.split 2 (.tip (.small 0)) (.tip (.cover 3 5 6 7))) (.tip (.cover 3 4 6 7))) (.tip (.cover 0 2 3 7))))
private theorem t8_36OK : treeOK shape8_8 16392 513 t8_36=true := by decide

private def t8_32 : Tree 8 := .split 3 t8_33 t8_36
private theorem t8_32OK : treeOK shape8_8 16384 513 t8_32=true := by
  change (treeOK shape8_8 16384 (513 ||| 2^3) t8_33 && treeOK shape8_8 (16384 ||| 2^3) 513 t8_36)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_33OK,t8_36OK⟩

private def t8_28 : Tree 8 := .split 14 t8_29 t8_32
private theorem t8_28OK : treeOK shape8_8 0 513 t8_28=true := by
  change (treeOK shape8_8 0 (513 ||| 2^14) t8_29 && treeOK shape8_8 (0 ||| 2^14) 513 t8_32)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_29OK,t8_32OK⟩

private def t8_40 : Tree 8 := (.split 2 (.tip (.small 0)) (.split 6 (.tip (.small 0)) (.tip (.cover 1 2 3 4))))
private theorem t8_40OK : treeOK shape8_8 512 16419 t8_40=true := by decide

private def t8_41 : Tree 8 := (.split 6 (.split 2 (.tip (.small 0)) (.split 3 (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2 4))) (.tip (.cover 0 1 2 4)))) (.split 2 (.split 7 (.split 8 (.tip (.small 1)) (.tip (.cover 2 4 5 7))) (.tip (.cover 2 4 5 6))) (.tip (.cover 1 2 3 4))))
private theorem t8_41OK : treeOK shape8_8 544 16387 t8_41=true := by decide

private def t8_39 : Tree 8 := .split 5 t8_40 t8_41
private theorem t8_39OK : treeOK shape8_8 512 16387 t8_39=true := by
  change (treeOK shape8_8 512 (16387 ||| 2^5) t8_40 && treeOK shape8_8 (512 ||| 2^5) 16387 t8_41)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_40OK,t8_41OK⟩

private def t8_42 : Tree 8 := (.split 2 (.split 5 (.split 6 (.tip (.small 0)) (.split 3 (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2 5))) (.tip (.cover 0 1 2 5)))) (.tip (.cover 1 2 3 5))) (.split 5 (.split 3 (.split 4 (.tip (.small 1)) (.tip (.cover 3 4 5 7))) (.tip (.cover 3 4 5 6))) (.tip (.cover 1 2 3 5))))
private theorem t8_42OK : treeOK shape8_8 514 16385 t8_42=true := by decide

private def t8_38 : Tree 8 := .split 1 t8_39 t8_42
private theorem t8_38OK : treeOK shape8_8 512 16385 t8_38=true := by
  change (treeOK shape8_8 512 (16385 ||| 2^1) t8_39 && treeOK shape8_8 (512 ||| 2^1) 16385 t8_42)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_39OK,t8_42OK⟩

private def t8_43 : Tree 8 := (.tip (.cover 2 3 4 6))
private theorem t8_43OK : treeOK shape8_8 16896 1 t8_43=true := by decide

private def t8_37 : Tree 8 := .split 14 t8_38 t8_43
private theorem t8_37OK : treeOK shape8_8 512 1 t8_37=true := by
  change (treeOK shape8_8 512 (1 ||| 2^14) t8_38 && treeOK shape8_8 (512 ||| 2^14) 1 t8_43)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_38OK,t8_43OK⟩

private def t8_27 : Tree 8 := .split 9 t8_28 t8_37
private theorem t8_27OK : treeOK shape8_8 0 1 t8_27=true := by
  change (treeOK shape8_8 0 (1 ||| 2^9) t8_28 && treeOK shape8_8 (0 ||| 2^9) 1 t8_37)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_28OK,t8_37OK⟩

private def t8_48 : Tree 8 := (.split 5 (.tip (.small 0)) (.split 7 (.split 8 (.tip (.rank 0)) (.split 9 (.tip (.small 0)) (.tip (.cover 0 2 4 7)))) (.split 8 (.split 9 (.tip (.small 0)) (.tip (.cover 0 2 4 6))) (.tip (.cover 0 2 6 7)))))
private theorem t8_48OK : treeOK shape8_8 1 16454 t8_48=true := by decide

private def t8_50 : Tree 8 := (.split 4 (.tip (.cover 0 2 6 7)) (.split 5 (.split 9 (.tip (.small 0)) (.tip (.cover 0 3 5 7))) (.split 8 (.split 9 (.tip (.rank 0)) (.tip (.cover 0 1 2 4))) (.tip (.cover 0 1 2 3)))))
private theorem t8_50OK : treeOK shape8_8 5 16458 t8_50=true := by decide

private def t8_51 : Tree 8 := (.split 4 (.split 5 (.split 9 (.tip (.small 0)) (.tip (.cover 0 3 5 6))) (.split 7 (.split 9 (.tip (.rank 0)) (.tip (.cover 0 1 2 4))) (.tip (.cover 0 1 2 3)))) (.tip (.cover 0 3 6 7)))
private theorem t8_51OK : treeOK shape8_8 13 16450 t8_51=true := by decide

private def t8_49 : Tree 8 := .split 3 t8_50 t8_51
private theorem t8_49OK : treeOK shape8_8 5 16450 t8_49=true := by
  change (treeOK shape8_8 5 (16450 ||| 2^3) t8_50 && treeOK shape8_8 (5 ||| 2^3) 16450 t8_51)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_50OK,t8_51OK⟩

private def t8_47 : Tree 8 := .split 2 t8_48 t8_49
private theorem t8_47OK : treeOK shape8_8 1 16450 t8_47=true := by
  change (treeOK shape8_8 1 (16450 ||| 2^2) t8_48 && treeOK shape8_8 (1 ||| 2^2) 16450 t8_49)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_48OK,t8_49OK⟩

private def t8_53 : Tree 8 := (.split 8 (.split 9 (.split 2 (.tip (.small 0)) (.split 4 (.split 5 (.tip (.small 0)) (.tip (.cover 0 2 3 6))) (.tip (.cover 1 3 5 7)))) (.tip (.cover 2 3 4 6))) (.split 4 (.split 5 (.split 9 (.tip (.small 0)) (.tip (.cover 1 2 4 7))) (.tip (.cover 1 2 4 7))) (.tip (.cover 0 2 3 6))))
private theorem t8_53OK : treeOK shape8_8 16385 74 t8_53=true := by decide

private def t8_54 : Tree 8 := (.split 4 (.split 7 (.split 9 (.split 2 (.tip (.small 0)) (.tip (.cover 1 3 5 6))) (.tip (.cover 1 3 4 6))) (.tip (.cover 0 2 3 7))) (.tip (.cover 0 3 6 7)))
private theorem t8_54OK : treeOK shape8_8 16393 66 t8_54=true := by decide

private def t8_52 : Tree 8 := .split 3 t8_53 t8_54
private theorem t8_52OK : treeOK shape8_8 16385 66 t8_52=true := by
  change (treeOK shape8_8 16385 (66 ||| 2^3) t8_53 && treeOK shape8_8 (16385 ||| 2^3) 66 t8_54)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_53OK,t8_54OK⟩

private def t8_46 : Tree 8 := .split 14 t8_47 t8_52
private theorem t8_46OK : treeOK shape8_8 1 66 t8_46=true := by
  change (treeOK shape8_8 1 (66 ||| 2^14) t8_47 && treeOK shape8_8 (1 ||| 2^14) 66 t8_52)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_47OK,t8_52OK⟩

private def t8_57 : Tree 8 := (.split 8 (.split 9 (.tip (.cover 1 2 4 5)) (.split 14 (.tip (.cover 0 3 6 7)) (.tip (.cover 0 2 5 6)))) (.split 9 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 2 5 7))))
private theorem t8_57OK : treeOK shape8_8 65 134 t8_57=true := by decide

private def t8_58 : Tree 8 := (.split 4 (.split 9 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 2 3 4))) (.split 8 (.split 9 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 1 2 5))) (.tip (.cover 0 1 2 3))))
private theorem t8_58OK : treeOK shape8_8 69 130 t8_58=true := by decide

private def t8_56 : Tree 8 := .split 2 t8_57 t8_58
private theorem t8_56OK : treeOK shape8_8 65 130 t8_56=true := by
  change (treeOK shape8_8 65 (130 ||| 2^2) t8_57 && treeOK shape8_8 (65 ||| 2^2) 130 t8_58)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_57OK,t8_58OK⟩

private def t8_59 : Tree 8 := (.split 8 (.split 2 (.split 9 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 2 5 6))) (.split 3 (.split 9 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 1 3 5))) (.tip (.cover 0 1 2 3)))) (.tip (.cover 0 2 6 7)))
private theorem t8_59OK : treeOK shape8_8 193 2 t8_59=true := by decide

private def t8_55 : Tree 8 := .split 7 t8_56 t8_59
private theorem t8_55OK : treeOK shape8_8 65 2 t8_55=true := by
  change (treeOK shape8_8 65 (2 ||| 2^7) t8_56 && treeOK shape8_8 (65 ||| 2^7) 2 t8_59)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_56OK,t8_59OK⟩

private def t8_45 : Tree 8 := .split 6 t8_46 t8_55
private theorem t8_45OK : treeOK shape8_8 1 2 t8_45=true := by
  change (treeOK shape8_8 1 (2 ||| 2^6) t8_46 && treeOK shape8_8 (1 ||| 2^6) 2 t8_55)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_46OK,t8_55OK⟩

private def t8_64 : Tree 8 := (.split 4 (.tip (.cover 0 2 6 7)) (.split 6 (.split 9 (.tip (.small 0)) (.tip (.cover 0 3 4 7))) (.split 8 (.split 9 (.tip (.rank 0)) (.tip (.cover 0 1 2 5))) (.tip (.cover 0 1 2 3)))))
private theorem t8_64OK : treeOK shape8_8 3 16428 t8_64=true := by decide

private def t8_65 : Tree 8 := (.split 4 (.split 6 (.split 9 (.tip (.small 0)) (.tip (.cover 0 3 4 6))) (.split 7 (.split 9 (.tip (.rank 0)) (.tip (.cover 0 1 2 5))) (.tip (.cover 0 1 2 3)))) (.tip (.cover 0 3 6 7)))
private theorem t8_65OK : treeOK shape8_8 11 16420 t8_65=true := by decide

private def t8_63 : Tree 8 := .split 3 t8_64 t8_65
private theorem t8_63OK : treeOK shape8_8 3 16420 t8_63=true := by
  change (treeOK shape8_8 3 (16420 ||| 2^3) t8_64 && treeOK shape8_8 (3 ||| 2^3) 16420 t8_65)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_64OK,t8_65OK⟩

private def t8_66 : Tree 8 := (.split 3 (.split 8 (.split 9 (.split 4 (.split 6 (.tip (.small 0)) (.tip (.cover 0 2 3 6))) (.tip (.cover 1 3 4 7))) (.tip (.cover 0 3 4 6))) (.tip (.cover 0 1 2 7))) (.tip (.cover 1 3 4 6)))
private theorem t8_66OK : treeOK shape8_8 16387 36 t8_66=true := by decide

private def t8_62 : Tree 8 := .split 14 t8_63 t8_66
private theorem t8_62OK : treeOK shape8_8 3 36 t8_62=true := by
  change (treeOK shape8_8 3 (36 ||| 2^14) t8_63 && treeOK shape8_8 (3 ||| 2^14) 36 t8_66)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_63OK,t8_66OK⟩

private def t8_67 : Tree 8 := (.split 7 (.split 4 (.split 9 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 2 3 5))) (.split 8 (.split 9 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 1 2 4))) (.tip (.cover 0 1 2 3)))) (.split 8 (.split 3 (.split 9 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 1 3 4))) (.tip (.cover 0 1 2 3))) (.tip (.cover 0 2 6 7))))
private theorem t8_67OK : treeOK shape8_8 35 4 t8_67=true := by decide

private def t8_61 : Tree 8 := .split 5 t8_62 t8_67
private theorem t8_61OK : treeOK shape8_8 3 4 t8_61=true := by
  change (treeOK shape8_8 3 (4 ||| 2^5) t8_62 && treeOK shape8_8 (3 ||| 2^5) 4 t8_67)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_62OK,t8_67OK⟩

private def t8_68 : Tree 8 := (.tip (.cover 1 3 4 5))
private theorem t8_68OK : treeOK shape8_8 7 0 t8_68=true := by decide

private def t8_60 : Tree 8 := .split 2 t8_61 t8_68
private theorem t8_60OK : treeOK shape8_8 3 0 t8_60=true := by
  change (treeOK shape8_8 3 (0 ||| 2^2) t8_61 && treeOK shape8_8 (3 ||| 2^2) 0 t8_68)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_61OK,t8_68OK⟩

private def t8_44 : Tree 8 := .split 1 t8_45 t8_60
private theorem t8_44OK : treeOK shape8_8 1 0 t8_44=true := by
  change (treeOK shape8_8 1 (0 ||| 2^1) t8_45 && treeOK shape8_8 (1 ||| 2^1) 0 t8_60)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_45OK,t8_60OK⟩

private def t8_26 : Tree 8 := .split 0 t8_27 t8_44
private theorem t8_26OK : treeOK shape8_8 0 0 t8_26=true := by
  change (treeOK shape8_8 0 (0 ||| 2^0) t8_27 && treeOK shape8_8 (0 ||| 2^0) 0 t8_44)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_27OK,t8_44OK⟩

private def shape8_9 : Shape := ⟨true,6,4,2⟩
private def t8_70 : Tree 8 := (.tip (.small 1))
private theorem t8_70OK : treeOK shape8_9 0 1 t8_70=true := by decide

private def t8_73 : Tree 8 := (.split 3 (.split 8 (.tip (.small 1)) (.split 10 (.tip (.cover 1 2 4 6)) (.split 4 (.tip (.small 1)) (.tip (.cover 1 2 3 4))))) (.split 4 (.tip (.small 1)) (.split 7 (.split 12 (.tip (.cover 1 3 5 6)) (.tip (.cover 0 3 6 7))) (.split 8 (.tip (.small 1)) (.tip (.cover 0 1 6 7))))))
private theorem t8_73OK : treeOK shape8_9 1 66 t8_73=true := by decide

private def t8_74 : Tree 8 := (.split 7 (.split 2 (.split 8 (.tip (.small 1)) (.split 9 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 2 5 7)))) (.split 4 (.tip (.small 1)) (.split 8 (.tip (.small 1)) (.tip (.cover 0 1 5 7))))) (.tip (.cover 1 2 5 6)))
private theorem t8_74OK : treeOK shape8_9 65 2 t8_74=true := by decide

private def t8_72 : Tree 8 := .split 6 t8_73 t8_74
private theorem t8_72OK : treeOK shape8_9 1 2 t8_72=true := by
  change (treeOK shape8_9 1 (2 ||| 2^6) t8_73 && treeOK shape8_9 (1 ||| 2^6) 2 t8_74)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_73OK,t8_74OK⟩

private def t8_75 : Tree 8 := (.split 2 (.split 5 (.split 3 (.split 8 (.tip (.small 1)) (.split 12 (.tip (.cover 1 2 5 6)) (.tip (.cover 1 2 3 5)))) (.tip (.cover 1 3 4 6))) (.split 7 (.split 4 (.tip (.small 1)) (.split 8 (.tip (.small 1)) (.tip (.cover 0 1 4 7)))) (.tip (.cover 1 2 4 6)))) (.tip (.cover 1 3 4 5)))
private theorem t8_75OK : treeOK shape8_9 3 0 t8_75=true := by decide

private def t8_71 : Tree 8 := .split 1 t8_72 t8_75
private theorem t8_71OK : treeOK shape8_9 1 0 t8_71=true := by
  change (treeOK shape8_9 1 (0 ||| 2^1) t8_72 && treeOK shape8_9 (1 ||| 2^1) 0 t8_75)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_72OK,t8_75OK⟩

private def t8_69 : Tree 8 := .split 0 t8_70 t8_71
private theorem t8_69OK : treeOK shape8_9 0 0 t8_69=true := by
  change (treeOK shape8_9 0 (0 ||| 2^0) t8_70 && treeOK shape8_9 (0 ||| 2^0) 0 t8_71)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_70OK,t8_71OK⟩

private def shape8_10 : Shape := ⟨true,4,4,3⟩
private def t8_77 : Tree 8 := (.split 1 (.tip (.small 0)) (.split 5 (.tip (.small 0)) (.split 9 (.tip (.cover 0 1 4 5)) (.split 10 (.tip (.cover 0 1 4 6)) (.split 11 (.tip (.cover 0 1 4 7)) (.split 12 (.tip (.cover 0 1 5 6)) (.tip (.cover 0 2 3 5))))))))
private theorem t8_77OK : treeOK shape8_10 0 1 t8_77=true := by decide

private def t8_79 : Tree 8 := (.split 5 (.tip (.small 0)) (.split 6 (.tip (.cover 0 1 3 5)) (.split 7 (.tip (.cover 0 1 3 6)) (.split 8 (.tip (.cover 0 1 3 7)) (.split 12 (.tip (.cover 0 1 5 6)) (.tip (.cover 0 2 4 5)))))))
private theorem t8_79OK : treeOK shape8_10 1 2 t8_79=true := by decide

private def t8_81 : Tree 8 := (.split 2 (.tip (.cover 0 1 2 5)) (.split 3 (.tip (.cover 0 1 2 6)) (.split 4 (.tip (.cover 0 1 2 7)) (.split 12 (.tip (.cover 0 1 5 6)) (.tip (.cover 0 3 4 5))))))
private theorem t8_81OK : treeOK shape8_10 3 32 t8_81=true := by decide

private def t8_82 : Tree 8 := (.split 2 (.tip (.cover 0 1 2 5)) (.split 3 (.tip (.cover 0 1 2 6)) (.split 4 (.tip (.cover 0 1 2 7)) (.split 6 (.tip (.cover 0 1 3 5)) (.tip (.cover 0 1 4 5))))))
private theorem t8_82OK : treeOK shape8_10 35 0 t8_82=true := by decide

private def t8_80 : Tree 8 := .split 5 t8_81 t8_82
private theorem t8_80OK : treeOK shape8_10 3 0 t8_80=true := by
  change (treeOK shape8_10 3 (0 ||| 2^5) t8_81 && treeOK shape8_10 (3 ||| 2^5) 0 t8_82)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_81OK,t8_82OK⟩

private def t8_78 : Tree 8 := .split 1 t8_79 t8_80
private theorem t8_78OK : treeOK shape8_10 1 0 t8_78=true := by
  change (treeOK shape8_10 1 (0 ||| 2^1) t8_79 && treeOK shape8_10 (1 ||| 2^1) 0 t8_80)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_79OK,t8_80OK⟩

private def t8_76 : Tree 8 := .split 0 t8_77 t8_78
private theorem t8_76OK : treeOK shape8_10 0 0 t8_76=true := by
  change (treeOK shape8_10 0 (0 ||| 2^0) t8_77 && treeOK shape8_10 (0 ||| 2^0) 0 t8_78)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_77OK,t8_78OK⟩

private def shape8_11 : Shape := ⟨true,5,4,3⟩
private def t8_84 : Tree 8 := (.split 1 (.tip (.small 1)) (.split 5 (.tip (.small 1)) (.split 9 (.split 14 (.tip (.cover 0 1 6 7)) (.split 2 (.split 6 (.tip (.cover 1 2 3 5)) (.split 7 (.tip (.cover 0 1 3 6)) (.tip (.cover 0 1 4 6)))) (.split 3 (.tip (.cover 0 1 2 6)) (.tip (.cover 0 1 4 6))))) (.tip (.cover 1 2 3 5)))))
private theorem t8_84OK : treeOK shape8_11 0 1 t8_84=true := by decide

private def t8_86 : Tree 8 := (.split 5 (.tip (.small 1)) (.split 6 (.split 14 (.tip (.cover 0 1 6 7)) (.split 2 (.split 7 (.tip (.cover 0 1 3 6)) (.tip (.cover 0 2 4 6))) (.split 3 (.tip (.cover 0 1 2 6)) (.tip (.cover 0 1 3 6))))) (.tip (.cover 1 2 4 5))))
private theorem t8_86OK : treeOK shape8_11 1 2 t8_86=true := by decide

private def t8_87 : Tree 8 := (.split 5 (.split 2 (.split 14 (.tip (.cover 0 1 6 7)) (.split 3 (.tip (.cover 0 1 2 6)) (.tip (.cover 0 3 4 6)))) (.tip (.cover 1 3 4 5))) (.split 2 (.split 6 (.tip (.cover 1 2 3 5)) (.tip (.cover 1 2 4 5))) (.tip (.cover 1 3 4 5))))
private theorem t8_87OK : treeOK shape8_11 3 0 t8_87=true := by decide

private def t8_85 : Tree 8 := .split 1 t8_86 t8_87
private theorem t8_85OK : treeOK shape8_11 1 0 t8_85=true := by
  change (treeOK shape8_11 1 (0 ||| 2^1) t8_86 && treeOK shape8_11 (1 ||| 2^1) 0 t8_87)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_86OK,t8_87OK⟩

private def t8_83 : Tree 8 := .split 0 t8_84 t8_85
private theorem t8_83OK : treeOK shape8_11 0 0 t8_83=true := by
  change (treeOK shape8_11 0 (0 ||| 2^0) t8_84 && treeOK shape8_11 (0 ||| 2^0) 0 t8_85)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_84OK,t8_85OK⟩

private def shape8_12 : Shape := ⟨true,5,5,3⟩
private def t8_91 : Tree 8 := (.split 12 (.split 13 (.split 14 (.tip (.rank 3)) (.tip (.cover 2 3 4 6))) (.tip (.cover 2 3 4 5))) (.tip (.cover 2 3 4 5)))
private theorem t8_91OK : treeOK shape8_12 0 35 t8_91=true := by decide

private def t8_94 : Tree 8 := (.split 2 (.split 14 (.split 9 (.tip (.small 0)) (.split 11 (.tip (.cover 0 1 4 7)) (.split 3 (.split 7 (.tip (.small 1)) (.tip (.rank 0))) (.tip (.cover 1 2 3 5))))) (.tip (.cover 2 3 4 6))) (.split 3 (.tip (.cover 0 2 4 6)) (.tip (.cover 3 4 5 6))))
private theorem t8_94OK : treeOK shape8_12 32 1091 t8_94=true := by decide

private def t8_95 : Tree 8 := (.split 14 (.split 2 (.split 9 (.tip (.small 0)) (.tip (.cover 2 3 5 6))) (.tip (.cover 0 2 3 6))) (.tip (.cover 2 3 4 6)))
private theorem t8_95OK : treeOK shape8_12 1056 67 t8_95=true := by decide

private def t8_93 : Tree 8 := .split 10 t8_94 t8_95
private theorem t8_93OK : treeOK shape8_12 32 67 t8_93=true := by
  change (treeOK shape8_12 32 (67 ||| 2^10) t8_94 && treeOK shape8_12 (32 ||| 2^10) 67 t8_95)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_94OK,t8_95OK⟩

private def t8_97 : Tree 8 := (.split 9 (.split 2 (.split 14 (.split 8 (.tip (.cover 0 1 3 7)) (.split 3 (.split 10 (.tip (.small 1)) (.tip (.rank 0))) (.tip (.cover 1 2 4 5)))) (.tip (.cover 2 3 4 6))) (.split 3 (.tip (.cover 0 2 3 6)) (.tip (.cover 0 1 2 3)))) (.split 13 (.tip (.cover 0 1 5 7)) (.tip (.cover 2 3 4 5))))
private theorem t8_97OK : treeOK shape8_12 96 131 t8_97=true := by decide

private def t8_98 : Tree 8 := (.tip (.cover 2 4 5 6))
private theorem t8_98OK : treeOK shape8_12 224 3 t8_98=true := by decide

private def t8_96 : Tree 8 := .split 7 t8_97 t8_98
private theorem t8_96OK : treeOK shape8_12 96 3 t8_96=true := by
  change (treeOK shape8_12 96 (3 ||| 2^7) t8_97 && treeOK shape8_12 (96 ||| 2^7) 3 t8_98)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_97OK,t8_98OK⟩

private def t8_92 : Tree 8 := .split 6 t8_93 t8_96
private theorem t8_92OK : treeOK shape8_12 32 3 t8_92=true := by
  change (treeOK shape8_12 32 (3 ||| 2^6) t8_93 && treeOK shape8_12 (32 ||| 2^6) 3 t8_96)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_93OK,t8_96OK⟩

private def t8_90 : Tree 8 := .split 5 t8_91 t8_92
private theorem t8_90OK : treeOK shape8_12 0 3 t8_90=true := by
  change (treeOK shape8_12 0 (3 ||| 2^5) t8_91 && treeOK shape8_12 (0 ||| 2^5) 3 t8_92)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_91OK,t8_92OK⟩

private def t8_102 : Tree 8 := (.split 6 (.split 14 (.split 9 (.tip (.small 0)) (.split 11 (.tip (.cover 0 1 4 7)) (.split 3 (.split 4 (.tip (.rank 0)) (.tip (.rank 0))) (.tip (.rank 0))))) (.tip (.cover 2 3 4 6))) (.split 7 (.tip (.cover 0 3 4 6)) (.tip (.cover 2 4 5 6))))
private theorem t8_102OK : treeOK shape8_12 2 1061 t8_102=true := by decide

private def t8_103 : Tree 8 := (.split 14 (.split 6 (.split 9 (.tip (.small 0)) (.tip (.cover 2 3 5 6))) (.tip (.cover 0 2 3 6))) (.tip (.cover 2 3 4 6)))
private theorem t8_103OK : treeOK shape8_12 1026 37 t8_103=true := by decide

private def t8_101 : Tree 8 := .split 10 t8_102 t8_103
private theorem t8_101OK : treeOK shape8_12 2 37 t8_101=true := by
  change (treeOK shape8_12 2 (37 ||| 2^10) t8_102 && treeOK shape8_12 (2 ||| 2^10) 37 t8_103)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_102OK,t8_103OK⟩

private def t8_105 : Tree 8 := (.split 9 (.split 6 (.split 14 (.split 4 (.tip (.cover 0 1 2 7)) (.split 7 (.split 10 (.tip (.small 1)) (.tip (.rank 0))) (.tip (.cover 1 3 4 5)))) (.tip (.cover 2 3 4 6))) (.split 7 (.tip (.cover 0 2 3 6)) (.tip (.cover 0 1 2 3)))) (.split 13 (.tip (.cover 0 1 5 7)) (.tip (.cover 2 3 4 5))))
private theorem t8_105OK : treeOK shape8_12 6 41 t8_105=true := by decide

private def t8_106 : Tree 8 := (.tip (.cover 3 4 5 6))
private theorem t8_106OK : treeOK shape8_12 14 33 t8_106=true := by decide

private def t8_104 : Tree 8 := .split 3 t8_105 t8_106
private theorem t8_104OK : treeOK shape8_12 6 33 t8_104=true := by
  change (treeOK shape8_12 6 (33 ||| 2^3) t8_105 && treeOK shape8_12 (6 ||| 2^3) 33 t8_106)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_105OK,t8_106OK⟩

private def t8_100 : Tree 8 := .split 2 t8_101 t8_104
private theorem t8_100OK : treeOK shape8_12 2 33 t8_100=true := by
  change (treeOK shape8_12 2 (33 ||| 2^2) t8_101 && treeOK shape8_12 (2 ||| 2^2) 33 t8_104)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_101OK,t8_104OK⟩

private def t8_107 : Tree 8 := (.split 9 (.split 3 (.split 7 (.tip (.cover 0 2 3 6)) (.split 6 (.tip (.cover 1 3 4 5)) (.tip (.cover 2 4 5 6)))) (.split 7 (.split 2 (.tip (.cover 1 2 4 5)) (.tip (.cover 3 4 5 6))) (.tip (.cover 0 1 2 3)))) (.tip (.cover 1 2 3 5)))
private theorem t8_107OK : treeOK shape8_12 34 1 t8_107=true := by decide

private def t8_99 : Tree 8 := .split 5 t8_100 t8_107
private theorem t8_99OK : treeOK shape8_12 2 1 t8_99=true := by
  change (treeOK shape8_12 2 (1 ||| 2^5) t8_100 && treeOK shape8_12 (2 ||| 2^5) 1 t8_107)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_100OK,t8_107OK⟩

private def t8_89 : Tree 8 := .split 1 t8_90 t8_99
private theorem t8_89OK : treeOK shape8_12 0 1 t8_89=true := by
  change (treeOK shape8_12 0 (1 ||| 2^1) t8_90 && treeOK shape8_12 (0 ||| 2^1) 1 t8_99)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_90OK,t8_99OK⟩

private def t8_112 : Tree 8 := (.split 9 (.split 14 (.split 6 (.tip (.small 0)) (.split 8 (.tip (.cover 0 1 3 7)) (.split 3 (.split 4 (.tip (.rank 0)) (.tip (.rank 0))) (.tip (.rank 0))))) (.tip (.cover 2 3 4 6))) (.split 10 (.tip (.cover 0 3 4 6)) (.tip (.cover 2 3 5 6))))
private theorem t8_112OK : treeOK shape8_12 1 166 t8_112=true := by decide

private def t8_113 : Tree 8 := (.split 14 (.split 6 (.split 9 (.tip (.small 0)) (.tip (.cover 0 2 4 6))) (.tip (.cover 2 4 5 6))) (.tip (.cover 2 3 4 6)))
private theorem t8_113OK : treeOK shape8_12 129 38 t8_113=true := by decide

private def t8_111 : Tree 8 := .split 7 t8_112 t8_113
private theorem t8_111OK : treeOK shape8_12 1 38 t8_111=true := by
  change (treeOK shape8_12 1 (38 ||| 2^7) t8_112 && treeOK shape8_12 (1 ||| 2^7) 38 t8_113)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_112OK,t8_113OK⟩

private def t8_115 : Tree 8 := (.split 6 (.split 9 (.split 14 (.split 4 (.tip (.cover 0 1 2 7)) (.split 7 (.split 8 (.tip (.rank 0)) (.tip (.rank 0))) (.tip (.rank 0)))) (.tip (.cover 2 3 4 6))) (.split 10 (.tip (.cover 0 2 4 6)) (.tip (.cover 0 1 2 4)))) (.split 13 (.tip (.cover 0 1 5 7)) (.tip (.cover 2 3 4 5))))
private theorem t8_115OK : treeOK shape8_12 5 42 t8_115=true := by decide

private def t8_116 : Tree 8 := (.tip (.cover 3 4 5 6))
private theorem t8_116OK : treeOK shape8_12 13 34 t8_116=true := by decide

private def t8_114 : Tree 8 := .split 3 t8_115 t8_116
private theorem t8_114OK : treeOK shape8_12 5 34 t8_114=true := by
  change (treeOK shape8_12 5 (34 ||| 2^3) t8_115 && treeOK shape8_12 (5 ||| 2^3) 34 t8_116)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_115OK,t8_116OK⟩

private def t8_110 : Tree 8 := .split 2 t8_111 t8_114
private theorem t8_110OK : treeOK shape8_12 1 34 t8_110=true := by
  change (treeOK shape8_12 1 (34 ||| 2^2) t8_111 && treeOK shape8_12 (1 ||| 2^2) 34 t8_114)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_111OK,t8_114OK⟩

private def t8_117 : Tree 8 := (.split 6 (.split 3 (.split 10 (.tip (.cover 0 2 4 6)) (.split 7 (.split 9 (.tip (.cover 1 3 4 5)) (.tip (.cover 2 3 5 6))) (.tip (.cover 0 2 4 6)))) (.split 7 (.split 2 (.tip (.cover 1 2 3 5)) (.tip (.cover 3 4 5 6))) (.tip (.cover 0 2 4 6)))) (.tip (.cover 1 2 4 5)))
private theorem t8_117OK : treeOK shape8_12 33 2 t8_117=true := by decide

private def t8_109 : Tree 8 := .split 5 t8_110 t8_117
private theorem t8_109OK : treeOK shape8_12 1 2 t8_109=true := by
  change (treeOK shape8_12 1 (2 ||| 2^5) t8_110 && treeOK shape8_12 (1 ||| 2^5) 2 t8_117)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_110OK,t8_117OK⟩

private def t8_119 : Tree 8 := (.split 2 (.split 3 (.split 6 (.split 9 (.tip (.cover 1 3 4 5)) (.split 10 (.tip (.cover 0 2 4 6)) (.tip (.cover 2 3 5 6)))) (.split 7 (.tip (.cover 0 2 3 6)) (.tip (.cover 2 4 5 6)))) (.tip (.cover 0 3 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t8_119OK : treeOK shape8_12 3 32 t8_119=true := by decide

private def t8_120 : Tree 8 := (.split 2 (.split 7 (.split 9 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 2 3 5))) (.tip (.cover 0 2 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t8_120OK : treeOK shape8_12 35 0 t8_120=true := by decide

private def t8_118 : Tree 8 := .split 5 t8_119 t8_120
private theorem t8_118OK : treeOK shape8_12 3 0 t8_118=true := by
  change (treeOK shape8_12 3 (0 ||| 2^5) t8_119 && treeOK shape8_12 (3 ||| 2^5) 0 t8_120)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_119OK,t8_120OK⟩

private def t8_108 : Tree 8 := .split 1 t8_109 t8_118
private theorem t8_108OK : treeOK shape8_12 1 0 t8_108=true := by
  change (treeOK shape8_12 1 (0 ||| 2^1) t8_109 && treeOK shape8_12 (1 ||| 2^1) 0 t8_118)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_109OK,t8_118OK⟩

private def t8_88 : Tree 8 := .split 0 t8_89 t8_108
private theorem t8_88OK : treeOK shape8_12 0 0 t8_88=true := by
  change (treeOK shape8_12 0 (0 ||| 2^0) t8_89 && treeOK shape8_12 (0 ||| 2^0) 0 t8_108)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_89OK,t8_108OK⟩

private def shape8_13 : Shape := ⟨true,6,4,3⟩
private def t8_122 : Tree 8 := (.split 1 (.tip (.small 1)) (.split 5 (.tip (.small 1)) (.split 9 (.split 3 (.split 7 (.tip (.cover 1 2 3 6)) (.split 6 (.tip (.cover 1 3 4 5)) (.tip (.cover 1 2 5 6)))) (.split 7 (.split 2 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 3 5 6))) (.tip (.cover 0 1 4 6)))) (.tip (.cover 1 2 3 5)))))
private theorem t8_122OK : treeOK shape8_13 0 1 t8_122=true := by decide

private def t8_124 : Tree 8 := (.split 5 (.tip (.small 1)) (.split 6 (.split 3 (.split 10 (.tip (.cover 1 2 4 6)) (.split 7 (.split 9 (.tip (.cover 1 3 4 5)) (.tip (.cover 1 2 5 6))) (.tip (.cover 1 2 4 6)))) (.split 7 (.split 12 (.tip (.cover 1 3 5 6)) (.tip (.cover 0 1 3 6))) (.tip (.cover 1 2 4 6)))) (.tip (.cover 1 2 4 5))))
private theorem t8_124OK : treeOK shape8_13 1 2 t8_124=true := by decide

private def t8_125 : Tree 8 := (.split 5 (.split 2 (.split 3 (.split 12 (.tip (.cover 1 2 5 6)) (.tip (.cover 1 3 4 5))) (.tip (.cover 1 3 4 6))) (.tip (.cover 1 3 4 5))) (.split 2 (.split 7 (.split 9 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 2 3 5))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 3 4 5))))
private theorem t8_125OK : treeOK shape8_13 3 0 t8_125=true := by decide

private def t8_123 : Tree 8 := .split 1 t8_124 t8_125
private theorem t8_123OK : treeOK shape8_13 1 0 t8_123=true := by
  change (treeOK shape8_13 1 (0 ||| 2^1) t8_124 && treeOK shape8_13 (1 ||| 2^1) 0 t8_125)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_124OK,t8_125OK⟩

private def t8_121 : Tree 8 := .split 0 t8_122 t8_123
private theorem t8_121OK : treeOK shape8_13 0 0 t8_121=true := by
  change (treeOK shape8_13 0 (0 ||| 2^0) t8_122 && treeOK shape8_13 (0 ||| 2^0) 0 t8_123)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_122OK,t8_123OK⟩

private def shape8_14 : Shape := ⟨true,6,5,3⟩
private def t8_131 : Tree 8 := (.split 8 (.tip (.small 1)) (.split 11 (.tip (.small 1)) (.split 6 (.split 7 (.tip (.cover 1 3 5 6)) (.tip (.cover 2 4 6 7))) (.tip (.cover 2 4 5 7)))))
private theorem t8_131OK : treeOK shape8_14 0 4147 t8_131=true := by decide

private def t8_132 : Tree 8 := (.split 8 (.split 11 (.tip (.small 1)) (.split 2 (.split 3 (.tip (.cover 1 2 5 6)) (.tip (.cover 3 4 6 7))) (.tip (.cover 3 4 5 7)))) (.split 11 (.split 2 (.split 3 (.tip (.cover 1 2 5 6)) (.tip (.cover 3 4 6 7))) (.tip (.cover 3 4 5 7))) (.tip (.cover 0 2 3 4))))
private theorem t8_132OK : treeOK shape8_14 16 4131 t8_132=true := by decide

private def t8_130 : Tree 8 := .split 4 t8_131 t8_132
private theorem t8_130OK : treeOK shape8_14 0 4131 t8_130=true := by
  change (treeOK shape8_14 0 (4131 ||| 2^4) t8_131 && treeOK shape8_14 (0 ||| 2^4) 4131 t8_132)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_131OK,t8_132OK⟩

private def t8_133 : Tree 8 := (.tip (.cover 2 3 4 5))
private theorem t8_133OK : treeOK shape8_14 4096 35 t8_133=true := by decide

private def t8_129 : Tree 8 := .split 12 t8_130 t8_133
private theorem t8_129OK : treeOK shape8_14 0 35 t8_129=true := by
  change (treeOK shape8_14 0 (35 ||| 2^12) t8_130 && treeOK shape8_14 (0 ||| 2^12) 35 t8_133)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_130OK,t8_133OK⟩

private def t8_137 : Tree 8 := (.split 9 (.split 10 (.tip (.cover 1 4 5 6)) (.split 7 (.split 11 (.tip (.small 1)) (.tip (.cover 2 3 6 7))) (.tip (.cover 1 4 5 6)))) (.split 10 (.split 6 (.split 11 (.tip (.small 1)) (.tip (.cover 2 3 5 7))) (.tip (.cover 1 4 5 6))) (.tip (.cover 1 3 5 6))))
private theorem t8_137OK : treeOK shape8_14 32 4371 t8_137=true := by decide

private def t8_138 : Tree 8 := (.split 9 (.split 10 (.tip (.cover 1 4 5 6)) (.tip (.cover 1 2 3 6))) (.tip (.cover 1 2 3 5)))
private theorem t8_138OK : treeOK shape8_14 48 4355 t8_138=true := by decide

private def t8_136 : Tree 8 := .split 4 t8_137 t8_138
private theorem t8_136OK : treeOK shape8_14 32 4355 t8_136=true := by
  change (treeOK shape8_14 32 (4355 ||| 2^4) t8_137 && treeOK shape8_14 (32 ||| 2^4) 4355 t8_138)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_137OK,t8_138OK⟩

private def t8_140 : Tree 8 := (.split 4 (.split 6 (.split 7 (.tip (.cover 1 3 5 6)) (.tip (.cover 2 4 6 7))) (.tip (.cover 2 4 5 7))) (.split 6 (.split 7 (.tip (.cover 1 3 5 6)) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 2 4 5))))
private theorem t8_140OK : treeOK shape8_14 288 6147 t8_140=true := by decide

private def t8_141 : Tree 8 := (.split 4 (.split 6 (.split 7 (.tip (.cover 1 3 5 6)) (.tip (.cover 2 4 6 7))) (.tip (.cover 2 4 5 7))) (.tip (.cover 0 2 3 4)))
private theorem t8_141OK : treeOK shape8_14 2336 4099 t8_141=true := by decide

private def t8_139 : Tree 8 := .split 11 t8_140 t8_141
private theorem t8_139OK : treeOK shape8_14 288 4099 t8_139=true := by
  change (treeOK shape8_14 288 (4099 ||| 2^11) t8_140 && treeOK shape8_14 (288 ||| 2^11) 4099 t8_141)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_140OK,t8_141OK⟩

private def t8_135 : Tree 8 := .split 8 t8_136 t8_139
private theorem t8_135OK : treeOK shape8_14 32 4099 t8_135=true := by
  change (treeOK shape8_14 32 (4099 ||| 2^8) t8_136 && treeOK shape8_14 (32 ||| 2^8) 4099 t8_139)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_136OK,t8_139OK⟩

private def t8_142 : Tree 8 := (.tip (.cover 2 3 4 5))
private theorem t8_142OK : treeOK shape8_14 4128 3 t8_142=true := by decide

private def t8_134 : Tree 8 := .split 12 t8_135 t8_142
private theorem t8_134OK : treeOK shape8_14 32 3 t8_134=true := by
  change (treeOK shape8_14 32 (3 ||| 2^12) t8_135 && treeOK shape8_14 (32 ||| 2^12) 3 t8_142)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_135OK,t8_142OK⟩

private def t8_128 : Tree 8 := .split 5 t8_129 t8_134
private theorem t8_128OK : treeOK shape8_14 0 3 t8_128=true := by
  change (treeOK shape8_14 0 (3 ||| 2^5) t8_129 && treeOK shape8_14 (0 ||| 2^5) 3 t8_134)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_129OK,t8_134OK⟩

private def t8_147 : Tree 8 := (.split 9 (.split 10 (.tip (.cover 1 4 5 6)) (.split 3 (.split 11 (.tip (.small 1)) (.tip (.cover 2 3 6 7))) (.tip (.cover 1 4 5 6)))) (.split 10 (.split 2 (.split 11 (.tip (.small 1)) (.tip (.cover 2 3 5 7))) (.tip (.cover 1 4 5 6))) (.tip (.cover 1 2 5 6))))
private theorem t8_147OK : treeOK shape8_14 2 4401 t8_147=true := by decide

private def t8_148 : Tree 8 := (.split 9 (.split 10 (.tip (.cover 1 4 5 6)) (.tip (.cover 1 2 3 6))) (.tip (.cover 1 2 3 5)))
private theorem t8_148OK : treeOK shape8_14 258 4145 t8_148=true := by decide

private def t8_146 : Tree 8 := .split 8 t8_147 t8_148
private theorem t8_146OK : treeOK shape8_14 2 4145 t8_146=true := by
  change (treeOK shape8_14 2 (4145 ||| 2^8) t8_147 && treeOK shape8_14 (2 ||| 2^8) 4145 t8_148)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_147OK,t8_148OK⟩

private def t8_149 : Tree 8 := (.split 11 (.split 2 (.split 3 (.tip (.cover 1 2 5 6)) (.tip (.cover 3 4 6 7))) (.tip (.cover 3 4 5 7))) (.split 2 (.split 3 (.tip (.cover 1 2 5 6)) (.tip (.cover 3 4 6 7))) (.tip (.cover 3 4 5 7))))
private theorem t8_149OK : treeOK shape8_14 18 4129 t8_149=true := by decide

private def t8_145 : Tree 8 := .split 4 t8_146 t8_149
private theorem t8_145OK : treeOK shape8_14 2 4129 t8_145=true := by
  change (treeOK shape8_14 2 (4129 ||| 2^4) t8_146 && treeOK shape8_14 (2 ||| 2^4) 4129 t8_149)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_146OK,t8_149OK⟩

private def t8_150 : Tree 8 := (.tip (.cover 2 3 4 5))
private theorem t8_150OK : treeOK shape8_14 4098 33 t8_150=true := by decide

private def t8_144 : Tree 8 := .split 12 t8_145 t8_150
private theorem t8_144OK : treeOK shape8_14 2 33 t8_144=true := by
  change (treeOK shape8_14 2 (33 ||| 2^12) t8_145 && treeOK shape8_14 (2 ||| 2^12) 33 t8_150)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_145OK,t8_150OK⟩

private def t8_151 : Tree 8 := (.split 9 (.split 3 (.split 7 (.tip (.cover 1 2 3 6)) (.split 8 (.split 4 (.tip (.cover 0 2 3 7)) (.tip (.cover 0 1 2 3))) (.tip (.cover 2 4 6 7)))) (.split 4 (.split 7 (.split 8 (.tip (.cover 0 2 3 7)) (.tip (.cover 0 1 2 3))) (.tip (.cover 0 1 2 3))) (.tip (.cover 3 4 6 7)))) (.tip (.cover 1 2 3 5)))
private theorem t8_151OK : treeOK shape8_14 34 1 t8_151=true := by decide

private def t8_143 : Tree 8 := .split 5 t8_144 t8_151
private theorem t8_143OK : treeOK shape8_14 2 1 t8_143=true := by
  change (treeOK shape8_14 2 (1 ||| 2^5) t8_144 && treeOK shape8_14 (2 ||| 2^5) 1 t8_151)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_144OK,t8_151OK⟩

private def t8_127 : Tree 8 := .split 1 t8_128 t8_143
private theorem t8_127OK : treeOK shape8_14 0 1 t8_127=true := by
  change (treeOK shape8_14 0 (1 ||| 2^1) t8_128 && treeOK shape8_14 (0 ||| 2^1) 1 t8_143)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_128OK,t8_143OK⟩

private def t8_157 : Tree 8 := (.split 7 (.tip (.cover 1 3 5 6)) (.split 11 (.split 3 (.split 8 (.tip (.small 1)) (.tip (.cover 2 4 6 7))) (.tip (.cover 1 3 5 6))) (.tip (.cover 1 2 4 6))))
private theorem t8_157OK : treeOK shape8_14 1 4210 t8_157=true := by decide

private def t8_158 : Tree 8 := (.split 7 (.split 11 (.split 2 (.split 8 (.tip (.small 1)) (.tip (.cover 2 4 5 7))) (.tip (.cover 1 3 5 6))) (.tip (.cover 1 2 4 5))) (.tip (.cover 1 2 5 6)))
private theorem t8_158OK : treeOK shape8_14 65 4146 t8_158=true := by decide

private def t8_156 : Tree 8 := .split 6 t8_157 t8_158
private theorem t8_156OK : treeOK shape8_14 1 4146 t8_156=true := by
  change (treeOK shape8_14 1 (4146 ||| 2^6) t8_157 && treeOK shape8_14 (1 ||| 2^6) 4146 t8_158)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_157OK,t8_158OK⟩

private def t8_159 : Tree 8 := (.split 8 (.split 2 (.split 3 (.tip (.cover 1 2 5 6)) (.tip (.cover 3 4 6 7))) (.tip (.cover 3 4 5 7))) (.split 2 (.split 3 (.tip (.cover 1 2 5 6)) (.tip (.cover 3 4 6 7))) (.tip (.cover 3 4 5 7))))
private theorem t8_159OK : treeOK shape8_14 17 4130 t8_159=true := by decide

private def t8_155 : Tree 8 := .split 4 t8_156 t8_159
private theorem t8_155OK : treeOK shape8_14 1 4130 t8_155=true := by
  change (treeOK shape8_14 1 (4130 ||| 2^4) t8_156 && treeOK shape8_14 (1 ||| 2^4) 4130 t8_159)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_156OK,t8_159OK⟩

private def t8_160 : Tree 8 := (.tip (.cover 2 3 4 5))
private theorem t8_160OK : treeOK shape8_14 4097 34 t8_160=true := by decide

private def t8_154 : Tree 8 := .split 12 t8_155 t8_160
private theorem t8_154OK : treeOK shape8_14 1 34 t8_154=true := by
  change (treeOK shape8_14 1 (34 ||| 2^12) t8_155 && treeOK shape8_14 (1 ||| 2^12) 34 t8_160)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_155OK,t8_160OK⟩

private def t8_161 : Tree 8 := (.split 6 (.split 3 (.split 8 (.split 10 (.tip (.cover 1 2 4 6)) (.split 9 (.tip (.cover 1 3 4 5)) (.tip (.cover 1 2 5 6)))) (.tip (.cover 0 2 4 7))) (.split 4 (.split 7 (.split 11 (.tip (.cover 0 2 4 7)) (.tip (.cover 0 1 2 4))) (.tip (.cover 1 2 4 6))) (.tip (.cover 3 4 6 7)))) (.tip (.cover 1 2 4 5)))
private theorem t8_161OK : treeOK shape8_14 33 2 t8_161=true := by decide

private def t8_153 : Tree 8 := .split 5 t8_154 t8_161
private theorem t8_153OK : treeOK shape8_14 1 2 t8_153=true := by
  change (treeOK shape8_14 1 (2 ||| 2^5) t8_154 && treeOK shape8_14 (1 ||| 2^5) 2 t8_161)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_154OK,t8_161OK⟩

private def t8_163 : Tree 8 := (.split 2 (.split 3 (.split 8 (.split 11 (.tip (.cover 0 3 4 7)) (.split 12 (.tip (.cover 1 2 5 6)) (.tip (.cover 1 2 4 5)))) (.split 11 (.split 12 (.tip (.cover 1 2 5 6)) (.tip (.cover 1 2 3 5))) (.tip (.cover 0 1 2 7)))) (.tip (.cover 1 3 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t8_163OK : treeOK shape8_14 3 32 t8_163=true := by decide

private def t8_164 : Tree 8 := (.split 2 (.split 7 (.split 11 (.split 3 (.tip (.cover 1 2 3 6)) (.tip (.cover 1 3 4 6))) (.tip (.cover 0 2 3 7))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t8_164OK : treeOK shape8_14 35 0 t8_164=true := by decide

private def t8_162 : Tree 8 := .split 5 t8_163 t8_164
private theorem t8_162OK : treeOK shape8_14 3 0 t8_162=true := by
  change (treeOK shape8_14 3 (0 ||| 2^5) t8_163 && treeOK shape8_14 (3 ||| 2^5) 0 t8_164)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_163OK,t8_164OK⟩

private def t8_152 : Tree 8 := .split 1 t8_153 t8_162
private theorem t8_152OK : treeOK shape8_14 1 0 t8_152=true := by
  change (treeOK shape8_14 1 (0 ||| 2^1) t8_153 && treeOK shape8_14 (1 ||| 2^1) 0 t8_162)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_153OK,t8_162OK⟩

private def t8_126 : Tree 8 := .split 0 t8_127 t8_152
private theorem t8_126OK : treeOK shape8_14 0 0 t8_126=true := by
  change (treeOK shape8_14 0 (0 ||| 2^0) t8_127 && treeOK shape8_14 (0 ||| 2^0) 0 t8_152)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_127OK,t8_152OK⟩

private def shape8_15 : Shape := ⟨true,7,4,3⟩
private def t8_167 : Tree 8 := (.tip (.small 1))
private theorem t8_167OK : treeOK shape8_15 0 3 t8_167=true := by decide

private def t8_169 : Tree 8 := (.tip (.small 1))
private theorem t8_169OK : treeOK shape8_15 2 33 t8_169=true := by decide

private def t8_170 : Tree 8 := (.split 9 (.split 14 (.split 2 (.split 6 (.tip (.cover 1 2 3 5)) (.split 7 (.split 8 (.tip (.cover 1 3 6 7)) (.tip (.cover 1 2 5 7))) (.tip (.cover 1 2 5 6)))) (.split 3 (.split 4 (.tip (.cover 1 2 6 7)) (.tip (.cover 1 3 5 7))) (.tip (.cover 1 3 5 6)))) (.tip (.cover 1 2 3 6))) (.tip (.cover 1 2 3 5)))
private theorem t8_170OK : treeOK shape8_15 34 1 t8_170=true := by decide

private def t8_168 : Tree 8 := .split 5 t8_169 t8_170
private theorem t8_168OK : treeOK shape8_15 2 1 t8_168=true := by
  change (treeOK shape8_15 2 (1 ||| 2^5) t8_169 && treeOK shape8_15 (2 ||| 2^5) 1 t8_170)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_169OK,t8_170OK⟩

private def t8_166 : Tree 8 := .split 1 t8_167 t8_168
private theorem t8_166OK : treeOK shape8_15 0 1 t8_166=true := by
  change (treeOK shape8_15 0 (1 ||| 2^1) t8_167 && treeOK shape8_15 (0 ||| 2^1) 1 t8_168)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_167OK,t8_168OK⟩

private def t8_172 : Tree 8 := (.split 5 (.tip (.small 1)) (.split 6 (.split 14 (.split 2 (.split 7 (.split 8 (.tip (.cover 1 3 6 7)) (.tip (.cover 1 2 4 7))) (.tip (.cover 1 2 4 6))) (.split 3 (.split 4 (.tip (.cover 1 2 6 7)) (.tip (.cover 1 3 5 7))) (.tip (.cover 1 3 5 6)))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 2 4 5))))
private theorem t8_172OK : treeOK shape8_15 1 2 t8_172=true := by decide

private def t8_174 : Tree 8 := (.split 2 (.split 14 (.split 3 (.split 4 (.tip (.cover 1 2 6 7)) (.tip (.cover 1 3 4 7))) (.tip (.cover 1 3 4 6))) (.tip (.cover 1 3 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t8_174OK : treeOK shape8_15 3 32 t8_174=true := by decide

private def t8_175 : Tree 8 := (.split 2 (.split 7 (.split 11 (.split 3 (.tip (.cover 1 2 3 6)) (.tip (.cover 1 3 4 6))) (.tip (.cover 1 2 3 7))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t8_175OK : treeOK shape8_15 35 0 t8_175=true := by decide

private def t8_173 : Tree 8 := .split 5 t8_174 t8_175
private theorem t8_173OK : treeOK shape8_15 3 0 t8_173=true := by
  change (treeOK shape8_15 3 (0 ||| 2^5) t8_174 && treeOK shape8_15 (3 ||| 2^5) 0 t8_175)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_174OK,t8_175OK⟩

private def t8_171 : Tree 8 := .split 1 t8_172 t8_173
private theorem t8_171OK : treeOK shape8_15 1 0 t8_171=true := by
  change (treeOK shape8_15 1 (0 ||| 2^1) t8_172 && treeOK shape8_15 (1 ||| 2^1) 0 t8_173)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_172OK,t8_173OK⟩

private def t8_165 : Tree 8 := .split 0 t8_166 t8_171
private theorem t8_165OK : treeOK shape8_15 0 0 t8_165=true := by
  change (treeOK shape8_15 0 (0 ||| 2^0) t8_166 && treeOK shape8_15 (0 ||| 2^0) 0 t8_171)=true
  rw [Bool.and_eq_true]
  exact ⟨t8_166OK,t8_171OK⟩

def forms8 : Fin 16 → Shape := ![⟨false,4,4,2⟩,⟨false,4,4,3⟩,⟨false,5,4,3⟩,⟨true,4,4,0⟩,⟨true,4,4,1⟩,⟨true,5,4,1⟩,⟨true,4,4,2⟩,⟨true,5,4,2⟩,⟨true,5,5,2⟩,⟨true,6,4,2⟩,⟨true,4,4,3⟩,⟨true,5,4,3⟩,⟨true,5,5,3⟩,⟨true,6,4,3⟩,⟨true,6,5,3⟩,⟨true,7,4,3⟩]

theorem check8 (i : Fin 16) (b : Nat→Bool)
    (H : Ranked (n:=8) (adj (forms8 i) b)) :
    ∃ a b' c d : Fin 8, Effective (adj (forms8 i) b) (adj (forms8 i) b) a b' c d := by
  fin_cases i
  · exact (checked_tree shape8_0 b H t8_0 t8_0OK)
  · exact (checked_tree shape8_1 b H t8_5 t8_5OK)
  · exact (checked_tree shape8_2 b H t8_8 t8_8OK)
  · exact (checked_tree shape8_3 b H t8_15 t8_15OK)
  · exact (checked_tree shape8_4 b H t8_16 t8_16OK)
  · exact (checked_tree shape8_5 b H t8_17 t8_17OK)
  · exact (checked_tree shape8_6 b H t8_18 t8_18OK)
  · exact (checked_tree shape8_7 b H t8_19 t8_19OK)
  · exact (checked_tree shape8_8 b H t8_26 t8_26OK)
  · exact (checked_tree shape8_9 b H t8_69 t8_69OK)
  · exact (checked_tree shape8_10 b H t8_76 t8_76OK)
  · exact (checked_tree shape8_11 b H t8_83 t8_83OK)
  · exact (checked_tree shape8_12 b H t8_88 t8_88OK)
  · exact (checked_tree shape8_13 b H t8_121 t8_121OK)
  · exact (checked_tree shape8_14 b H t8_126 t8_126OK)
  · exact (checked_tree shape8_15 b H t8_165 t8_165OK)
#print axioms check8
end Graffiti384b.SmallPalette
