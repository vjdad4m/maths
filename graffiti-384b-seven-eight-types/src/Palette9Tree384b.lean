import SmallPalette384b
import Mathlib.Tactic.FinCases
namespace Graffiti384b.SmallPalette
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 500000

private def shape9_0 : Shape := ⟨false,4,4,1⟩
private def t9_2 : Tree 9 := (.tip (.small 0))
private theorem t9_2OK : treeOK shape9_0 0 2049 t9_2=true := by decide

private def t9_4 : Tree 9 := (.split 1 (.tip (.small 0)) (.split 2 (.tip (.small 0)) (.split 5 (.tip (.small 1)) (.split 6 (.tip (.small 0)) (.tip (.cover 0 1 2 4))))))
private theorem t9_4OK : treeOK shape9_0 2048 262145 t9_4=true := by decide

private def t9_5 : Tree 9 := (.split 19 (.split 1 (.tip (.small 0)) (.split 2 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 4 7))))) (.tip (.cover 2 4 7 8)))
private theorem t9_5OK : treeOK shape9_0 264192 1 t9_5=true := by decide

private def t9_3 : Tree 9 := .split 18 t9_4 t9_5
private theorem t9_3OK : treeOK shape9_0 2048 1 t9_3=true := by
  change (treeOK shape9_0 2048 (1 ||| 2^18) t9_4 && treeOK shape9_0 (2048 ||| 2^18) 1 t9_5)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_4OK,t9_5OK⟩

private def t9_1 : Tree 9 := .split 11 t9_2 t9_3
private theorem t9_1OK : treeOK shape9_0 0 1 t9_1=true := by
  change (treeOK shape9_0 0 (1 ||| 2^11) t9_2 && treeOK shape9_0 (0 ||| 2^11) 1 t9_3)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_2OK,t9_3OK⟩

private def t9_7 : Tree 9 := (.split 7 (.tip (.small 0)) (.split 18 (.split 2 (.tip (.small 0)) (.split 5 (.tip (.small 1)) (.split 6 (.tip (.small 0)) (.tip (.cover 0 1 2 3))))) (.split 19 (.split 2 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 3 7)))) (.tip (.cover 0 1 3 6)))))
private theorem t9_7OK : treeOK shape9_0 1 2 t9_7=true := by decide

private def t9_8 : Tree 9 := (.split 2 (.split 6 (.tip (.small 0)) (.split 18 (.split 5 (.tip (.small 1)) (.split 7 (.tip (.small 0)) (.tip (.cover 0 1 2 3)))) (.split 19 (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 3 7))) (.tip (.cover 0 1 2 6))))) (.tip (.cover 1 3 4 5)))
private theorem t9_8OK : treeOK shape9_0 3 0 t9_8=true := by decide

private def t9_6 : Tree 9 := .split 1 t9_7 t9_8
private theorem t9_6OK : treeOK shape9_0 1 0 t9_6=true := by
  change (treeOK shape9_0 1 (0 ||| 2^1) t9_7 && treeOK shape9_0 (1 ||| 2^1) 0 t9_8)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_7OK,t9_8OK⟩

private def t9_0 : Tree 9 := .split 0 t9_1 t9_6
private theorem t9_0OK : treeOK shape9_0 0 0 t9_0=true := by
  change (treeOK shape9_0 0 (0 ||| 2^0) t9_1 && treeOK shape9_0 (0 ||| 2^0) 0 t9_6)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_1OK,t9_6OK⟩

private def shape9_1 : Shape := ⟨false,4,4,2⟩
private def t9_10 : Tree 9 := (.split 11 (.tip (.small 0)) (.split 18 (.tip (.small 1)) (.tip (.cover 2 3 4 6))))
private theorem t9_10OK : treeOK shape9_1 0 1 t9_10=true := by decide

private def t9_12 : Tree 9 := (.split 7 (.tip (.small 0)) (.split 8 (.split 2 (.tip (.small 0)) (.split 4 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.cover 0 1 2 3))))) (.split 9 (.split 2 (.tip (.small 0)) (.split 3 (.tip (.small 1)) (.tip (.cover 0 1 2 3)))) (.tip (.cover 0 2 6 7)))))
private theorem t9_12OK : treeOK shape9_1 1 2 t9_12=true := by decide

private def t9_13 : Tree 9 := (.split 2 (.split 6 (.tip (.small 0)) (.split 8 (.split 4 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.cover 0 1 2 3)))) (.split 9 (.split 3 (.tip (.small 1)) (.tip (.cover 0 1 2 3))) (.tip (.cover 0 2 6 7))))) (.tip (.cover 1 3 4 5)))
private theorem t9_13OK : treeOK shape9_1 3 0 t9_13=true := by decide

private def t9_11 : Tree 9 := .split 1 t9_12 t9_13
private theorem t9_11OK : treeOK shape9_1 1 0 t9_11=true := by
  change (treeOK shape9_1 1 (0 ||| 2^1) t9_12 && treeOK shape9_1 (1 ||| 2^1) 0 t9_13)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_12OK,t9_13OK⟩

private def t9_9 : Tree 9 := .split 0 t9_10 t9_11
private theorem t9_9OK : treeOK shape9_1 0 0 t9_9=true := by
  change (treeOK shape9_1 0 (0 ||| 2^0) t9_10 && treeOK shape9_1 (0 ||| 2^0) 0 t9_11)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_10OK,t9_11OK⟩

private def shape9_2 : Shape := ⟨false,5,4,2⟩
private def t9_17 : Tree 9 := (.tip (.small 1))
private theorem t9_17OK : treeOK shape9_2 0 1050625 t9_17=true := by decide

private def t9_19 : Tree 9 := (.split 8 (.split 4 (.tip (.small 1)) (.split 5 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.cover 0 2 3 8))))) (.split 9 (.tip (.small 1)) (.split 10 (.tip (.small 1)) (.tip (.cover 2 6 7 8)))))
private theorem t9_19OK : treeOK shape9_2 1048576 2057 t9_19=true := by decide

private def t9_20 : Tree 9 := (.split 4 (.tip (.small 1)) (.split 5 (.tip (.small 1)) (.tip (.cover 3 6 7 8))))
private theorem t9_20OK : treeOK shape9_2 1048584 2049 t9_20=true := by decide

private def t9_18 : Tree 9 := .split 3 t9_19 t9_20
private theorem t9_18OK : treeOK shape9_2 1048576 2049 t9_18=true := by
  change (treeOK shape9_2 1048576 (2049 ||| 2^3) t9_19 && treeOK shape9_2 (1048576 ||| 2^3) 2049 t9_20)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_19OK,t9_20OK⟩

private def t9_16 : Tree 9 := .split 20 t9_17 t9_18
private theorem t9_16OK : treeOK shape9_2 0 2049 t9_16=true := by
  change (treeOK shape9_2 0 (2049 ||| 2^20) t9_17 && treeOK shape9_2 (0 ||| 2^20) 2049 t9_18)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_17OK,t9_18OK⟩

private def t9_21 : Tree 9 := (.split 12 (.split 20 (.tip (.small 1)) (.tip (.cover 2 3 4 7))) (.tip (.cover 2 3 5 6)))
private theorem t9_21OK : treeOK shape9_2 2048 1 t9_21=true := by decide

private def t9_15 : Tree 9 := .split 11 t9_16 t9_21
private theorem t9_15OK : treeOK shape9_2 0 1 t9_15=true := by
  change (treeOK shape9_2 0 (1 ||| 2^11) t9_16 && treeOK shape9_2 (0 ||| 2^11) 1 t9_21)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_16OK,t9_21OK⟩

private def t9_26 : Tree 9 := (.split 12 (.tip (.cover 1 2 4 6)) (.split 6 (.split 11 (.tip (.cover 1 3 4 5)) (.tip (.cover 1 2 5 6))) (.split 8 (.split 11 (.tip (.cover 1 3 4 5)) (.tip (.cover 1 2 5 6))) (.tip (.cover 1 2 4 6)))))
private theorem t9_26OK : treeOK shape9_2 1 1048714 t9_26=true := by decide

private def t9_27 : Tree 9 := (.split 8 (.split 15 (.tip (.cover 1 3 5 6)) (.split 2 (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 1 2 5))) (.tip (.cover 1 3 5 6)))) (.split 12 (.tip (.cover 1 2 4 6)) (.tip (.cover 1 2 3 4))))
private theorem t9_27OK : treeOK shape9_2 9 1048706 t9_27=true := by decide

private def t9_25 : Tree 9 := .split 3 t9_26 t9_27
private theorem t9_25OK : treeOK shape9_2 1 1048706 t9_25=true := by
  change (treeOK shape9_2 1 (1048706 ||| 2^3) t9_26 && treeOK shape9_2 (1 ||| 2^3) 1048706 t9_27)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_26OK,t9_27OK⟩

private def t9_28 : Tree 9 := (.split 3 (.split 9 (.split 12 (.tip (.cover 1 2 4 6)) (.tip (.cover 2 3 4 7))) (.split 10 (.split 12 (.tip (.cover 1 2 4 6)) (.tip (.cover 1 2 4 7))) (.tip (.cover 0 2 7 8)))) (.split 4 (.split 8 (.split 15 (.tip (.cover 1 3 5 6)) (.tip (.cover 0 3 6 7))) (.tip (.cover 0 2 3 7))) (.tip (.cover 1 3 6 7))))
private theorem t9_28OK : treeOK shape9_2 1048577 130 t9_28=true := by decide

private def t9_24 : Tree 9 := .split 20 t9_25 t9_28
private theorem t9_24OK : treeOK shape9_2 1 130 t9_24=true := by
  change (treeOK shape9_2 1 (130 ||| 2^20) t9_25 && treeOK shape9_2 (1 ||| 2^20) 130 t9_28)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_25OK,t9_28OK⟩

private def t9_31 : Tree 9 := (.split 2 (.split 11 (.tip (.cover 1 2 4 5)) (.split 6 (.split 12 (.tip (.cover 1 3 4 6)) (.tip (.cover 0 1 3 4))) (.tip (.cover 1 2 4 5)))) (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 2 3 4))))
private theorem t9_31OK : treeOK shape9_2 129 1048834 t9_31=true := by decide

private def t9_32 : Tree 9 := (.split 2 (.split 9 (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 2 5 7))) (.tip (.cover 1 2 5 7))) (.tip (.cover 0 2 3 7)))
private theorem t9_32OK : treeOK shape9_2 1048705 258 t9_32=true := by decide

private def t9_30 : Tree 9 := .split 20 t9_31 t9_32
private theorem t9_30OK : treeOK shape9_2 129 258 t9_30=true := by
  change (treeOK shape9_2 129 (258 ||| 2^20) t9_31 && treeOK shape9_2 (129 ||| 2^20) 258 t9_32)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_31OK,t9_32OK⟩

private def t9_33 : Tree 9 := (.tip (.cover 1 2 5 6))
private theorem t9_33OK : treeOK shape9_2 385 2 t9_33=true := by decide

private def t9_29 : Tree 9 := .split 8 t9_30 t9_33
private theorem t9_29OK : treeOK shape9_2 129 2 t9_29=true := by
  change (treeOK shape9_2 129 (2 ||| 2^8) t9_30 && treeOK shape9_2 (129 ||| 2^8) 2 t9_33)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_30OK,t9_33OK⟩

private def t9_23 : Tree 9 := .split 7 t9_24 t9_29
private theorem t9_23OK : treeOK shape9_2 1 2 t9_23=true := by
  change (treeOK shape9_2 1 (2 ||| 2^7) t9_24 && treeOK shape9_2 (1 ||| 2^7) 2 t9_29)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_24OK,t9_29OK⟩

private def t9_36 : Tree 9 := (.split 20 (.split 3 (.split 15 (.tip (.cover 1 2 5 6)) (.tip (.cover 1 3 4 5))) (.tip (.cover 1 3 4 6))) (.split 3 (.split 9 (.split 15 (.tip (.cover 1 2 5 6)) (.tip (.cover 1 3 4 5))) (.tip (.cover 0 1 2 7))) (.tip (.cover 1 3 4 6))))
private theorem t9_36OK : treeOK shape9_2 3 68 t9_36=true := by decide

private def t9_37 : Tree 9 := (.split 8 (.split 20 (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 2 3 5))) (.tip (.cover 0 2 3 7))) (.tip (.cover 1 2 4 6)))
private theorem t9_37OK : treeOK shape9_2 67 4 t9_37=true := by decide

private def t9_35 : Tree 9 := .split 6 t9_36 t9_37
private theorem t9_35OK : treeOK shape9_2 3 4 t9_35=true := by
  change (treeOK shape9_2 3 (4 ||| 2^6) t9_36 && treeOK shape9_2 (3 ||| 2^6) 4 t9_37)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_36OK,t9_37OK⟩

private def t9_38 : Tree 9 := (.tip (.cover 1 3 4 5))
private theorem t9_38OK : treeOK shape9_2 7 0 t9_38=true := by decide

private def t9_34 : Tree 9 := .split 2 t9_35 t9_38
private theorem t9_34OK : treeOK shape9_2 3 0 t9_34=true := by
  change (treeOK shape9_2 3 (0 ||| 2^2) t9_35 && treeOK shape9_2 (3 ||| 2^2) 0 t9_38)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_35OK,t9_38OK⟩

private def t9_22 : Tree 9 := .split 1 t9_23 t9_34
private theorem t9_22OK : treeOK shape9_2 1 0 t9_22=true := by
  change (treeOK shape9_2 1 (0 ||| 2^1) t9_23 && treeOK shape9_2 (1 ||| 2^1) 0 t9_34)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_23OK,t9_34OK⟩

private def t9_14 : Tree 9 := .split 0 t9_15 t9_22
private theorem t9_14OK : treeOK shape9_2 0 0 t9_14=true := by
  change (treeOK shape9_2 0 (0 ||| 2^0) t9_15 && treeOK shape9_2 (0 ||| 2^0) 0 t9_22)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_15OK,t9_22OK⟩

private def shape9_3 : Shape := ⟨false,4,4,3⟩
private def t9_40 : Tree 9 := (.split 1 (.tip (.small 0)) (.split 6 (.tip (.small 0)) (.split 11 (.tip (.small 0)) (.tip (.cover 1 2 3 5)))))
private theorem t9_40OK : treeOK shape9_3 0 1 t9_40=true := by decide

private def t9_41 : Tree 9 := (.split 1 (.split 6 (.tip (.small 0)) (.split 7 (.tip (.small 0)) (.tip (.cover 1 2 4 5)))) (.split 6 (.split 2 (.tip (.small 0)) (.tip (.cover 1 3 4 5))) (.split 2 (.split 8 (.split 11 (.tip (.small 0)) (.tip (.cover 1 2 3 5))) (.tip (.cover 0 2 4 6))) (.tip (.cover 1 3 4 5)))))
private theorem t9_41OK : treeOK shape9_3 1 0 t9_41=true := by decide

private def t9_39 : Tree 9 := .split 0 t9_40 t9_41
private theorem t9_39OK : treeOK shape9_3 0 0 t9_39=true := by
  change (treeOK shape9_3 0 (0 ||| 2^0) t9_40 && treeOK shape9_3 (0 ||| 2^0) 0 t9_41)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_40OK,t9_41OK⟩

private def shape9_4 : Shape := ⟨false,5,4,3⟩
private def t9_43 : Tree 9 := (.split 1 (.tip (.small 1)) (.split 6 (.tip (.small 1)) (.split 11 (.split 3 (.split 8 (.tip (.cover 1 2 3 6)) (.split 9 (.tip (.small 1)) (.tip (.cover 2 4 6 7)))) (.split 4 (.tip (.small 1)) (.tip (.cover 3 4 6 7)))) (.tip (.cover 1 2 3 5)))))
private theorem t9_43OK : treeOK shape9_4 0 1 t9_43=true := by decide

private def t9_45 : Tree 9 := (.split 6 (.tip (.small 1)) (.split 7 (.split 3 (.split 9 (.tip (.small 1)) (.tip (.cover 0 2 4 7))) (.split 4 (.tip (.small 1)) (.tip (.cover 3 4 6 7)))) (.tip (.cover 1 2 4 5))))
private theorem t9_45OK : treeOK shape9_4 1 2 t9_45=true := by decide

private def t9_47 : Tree 9 := (.split 2 (.split 3 (.split 9 (.tip (.small 1)) (.split 13 (.tip (.small 1)) (.tip (.cover 0 1 2 7)))) (.tip (.cover 1 3 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t9_47OK : treeOK shape9_4 3 64 t9_47=true := by decide

private def t9_48 : Tree 9 := (.split 2 (.split 8 (.split 13 (.split 3 (.tip (.cover 1 2 3 6)) (.tip (.cover 1 3 4 6))) (.tip (.cover 0 2 3 7))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t9_48OK : treeOK shape9_4 67 0 t9_48=true := by decide

private def t9_46 : Tree 9 := .split 6 t9_47 t9_48
private theorem t9_46OK : treeOK shape9_4 3 0 t9_46=true := by
  change (treeOK shape9_4 3 (0 ||| 2^6) t9_47 && treeOK shape9_4 (3 ||| 2^6) 0 t9_48)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_47OK,t9_48OK⟩

private def t9_44 : Tree 9 := .split 1 t9_45 t9_46
private theorem t9_44OK : treeOK shape9_4 1 0 t9_44=true := by
  change (treeOK shape9_4 1 (0 ||| 2^1) t9_45 && treeOK shape9_4 (1 ||| 2^1) 0 t9_46)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_45OK,t9_46OK⟩

private def t9_42 : Tree 9 := .split 0 t9_43 t9_44
private theorem t9_42OK : treeOK shape9_4 0 0 t9_42=true := by
  change (treeOK shape9_4 0 (0 ||| 2^0) t9_43 && treeOK shape9_4 (0 ||| 2^0) 0 t9_44)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_43OK,t9_44OK⟩

private def shape9_5 : Shape := ⟨false,5,5,3⟩
private def t9_53 : Tree 9 := (.split 20 (.split 2 (.split 3 (.tip (.small 0)) (.split 7 (.tip (.small 0)) (.split 8 (.tip (.small 0)) (.tip (.cover 2 4 5 6))))) (.split 3 (.split 7 (.tip (.small 0)) (.split 8 (.tip (.small 0)) (.tip (.cover 2 4 5 6)))) (.tip (.cover 3 4 5 6)))) (.tip (.cover 2 3 4 7)))
private theorem t9_53OK : treeOK shape9_5 0 32835 t9_53=true := by decide

private def t9_54 : Tree 9 := (.tip (.cover 2 3 4 5))
private theorem t9_54OK : treeOK shape9_5 32768 67 t9_54=true := by decide

private def t9_52 : Tree 9 := .split 15 t9_53 t9_54
private theorem t9_52OK : treeOK shape9_5 0 67 t9_52=true := by
  change (treeOK shape9_5 0 (67 ||| 2^15) t9_53 && treeOK shape9_5 (0 ||| 2^15) 67 t9_54)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_53OK,t9_54OK⟩

private def t9_56 : Tree 9 := (.split 20 (.split 7 (.split 8 (.tip (.cover 1 3 5 6)) (.split 12 (.split 2 (.tip (.small 0)) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 3 5 6)))) (.split 8 (.split 11 (.split 2 (.tip (.small 0)) (.tip (.cover 1 3 5 6))) (.tip (.cover 1 3 5 6))) (.tip (.cover 1 4 5 6)))) (.tip (.cover 2 3 4 7)))
private theorem t9_56OK : treeOK shape9_5 64 32771 t9_56=true := by decide

private def t9_57 : Tree 9 := (.tip (.cover 2 3 4 5))
private theorem t9_57OK : treeOK shape9_5 32832 3 t9_57=true := by decide

private def t9_55 : Tree 9 := .split 15 t9_56 t9_57
private theorem t9_55OK : treeOK shape9_5 64 3 t9_55=true := by
  change (treeOK shape9_5 64 (3 ||| 2^15) t9_56 && treeOK shape9_5 (64 ||| 2^15) 3 t9_57)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_56OK,t9_57OK⟩

private def t9_51 : Tree 9 := .split 6 t9_52 t9_55
private theorem t9_51OK : treeOK shape9_5 0 3 t9_51=true := by
  change (treeOK shape9_5 0 (3 ||| 2^6) t9_52 && treeOK shape9_5 (0 ||| 2^6) 3 t9_55)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_52OK,t9_55OK⟩

private def t9_62 : Tree 9 := (.split 3 (.tip (.cover 1 2 5 6)) (.split 12 (.split 4 (.split 5 (.tip (.cover 0 2 7 8)) (.tip (.cover 3 4 6 8))) (.tip (.cover 3 4 6 7))) (.tip (.cover 1 2 5 6))))
private theorem t9_62OK : treeOK shape9_5 2 1081413 t9_62=true := by decide

private def t9_63 : Tree 9 := (.split 3 (.split 11 (.split 4 (.split 5 (.tip (.cover 0 2 7 8)) (.tip (.cover 3 4 5 8))) (.tip (.cover 3 4 5 7))) (.tip (.cover 1 2 5 6))) (.tip (.cover 1 4 5 6)))
private theorem t9_63OK : treeOK shape9_5 6 1081409 t9_63=true := by decide

private def t9_61 : Tree 9 := .split 2 t9_62 t9_63
private theorem t9_61OK : treeOK shape9_5 2 1081409 t9_61=true := by
  change (treeOK shape9_5 2 (1081409 ||| 2^2) t9_62 && treeOK shape9_5 (2 ||| 2^2) 1081409 t9_63)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_62OK,t9_63OK⟩

private def t9_64 : Tree 9 := (.tip (.cover 2 3 4 7))
private theorem t9_64OK : treeOK shape9_5 1048578 32833 t9_64=true := by decide

private def t9_60 : Tree 9 := .split 20 t9_61 t9_64
private theorem t9_60OK : treeOK shape9_5 2 32833 t9_60=true := by
  change (treeOK shape9_5 2 (32833 ||| 2^20) t9_61 && treeOK shape9_5 (2 ||| 2^20) 32833 t9_64)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_61OK,t9_64OK⟩

private def t9_65 : Tree 9 := (.tip (.cover 2 3 4 5))
private theorem t9_65OK : treeOK shape9_5 32770 65 t9_65=true := by decide

private def t9_59 : Tree 9 := .split 15 t9_60 t9_65
private theorem t9_59OK : treeOK shape9_5 2 65 t9_59=true := by
  change (treeOK shape9_5 2 (65 ||| 2^15) t9_60 && treeOK shape9_5 (2 ||| 2^15) 65 t9_65)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_60OK,t9_65OK⟩

private def t9_66 : Tree 9 := (.split 11 (.split 20 (.split 3 (.split 8 (.tip (.cover 1 2 3 6)) (.split 7 (.tip (.cover 1 3 4 5)) (.tip (.cover 1 2 5 6)))) (.split 8 (.split 2 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 3 5 6))) (.tip (.cover 0 1 2 3)))) (.tip (.cover 0 2 3 7))) (.tip (.cover 1 2 3 5)))
private theorem t9_66OK : treeOK shape9_5 66 1 t9_66=true := by decide

private def t9_58 : Tree 9 := .split 6 t9_59 t9_66
private theorem t9_58OK : treeOK shape9_5 2 1 t9_58=true := by
  change (treeOK shape9_5 2 (1 ||| 2^6) t9_59 && treeOK shape9_5 (2 ||| 2^6) 1 t9_66)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_59OK,t9_66OK⟩

private def t9_50 : Tree 9 := .split 1 t9_51 t9_58
private theorem t9_50OK : treeOK shape9_5 0 1 t9_50=true := by
  change (treeOK shape9_5 0 (1 ||| 2^1) t9_51 && treeOK shape9_5 (0 ||| 2^1) 1 t9_58)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_51OK,t9_58OK⟩

private def t9_72 : Tree 9 := (.split 3 (.tip (.cover 1 2 5 6)) (.split 8 (.split 4 (.split 5 (.tip (.cover 0 2 7 8)) (.tip (.cover 3 4 6 8))) (.tip (.cover 3 4 6 7))) (.tip (.cover 1 2 5 6))))
private theorem t9_72OK : treeOK shape9_5 1 1081414 t9_72=true := by decide

private def t9_73 : Tree 9 := (.split 3 (.split 7 (.split 4 (.split 5 (.tip (.cover 0 2 7 8)) (.tip (.cover 3 4 5 8))) (.tip (.cover 3 4 5 7))) (.tip (.cover 1 2 5 6))) (.tip (.cover 1 3 5 6)))
private theorem t9_73OK : treeOK shape9_5 5 1081410 t9_73=true := by decide

private def t9_71 : Tree 9 := .split 2 t9_72 t9_73
private theorem t9_71OK : treeOK shape9_5 1 1081410 t9_71=true := by
  change (treeOK shape9_5 1 (1081410 ||| 2^2) t9_72 && treeOK shape9_5 (1 ||| 2^2) 1081410 t9_73)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_72OK,t9_73OK⟩

private def t9_74 : Tree 9 := (.tip (.cover 2 3 4 7))
private theorem t9_74OK : treeOK shape9_5 1048577 32834 t9_74=true := by decide

private def t9_70 : Tree 9 := .split 20 t9_71 t9_74
private theorem t9_70OK : treeOK shape9_5 1 32834 t9_70=true := by
  change (treeOK shape9_5 1 (32834 ||| 2^20) t9_71 && treeOK shape9_5 (1 ||| 2^20) 32834 t9_74)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_71OK,t9_74OK⟩

private def t9_75 : Tree 9 := (.tip (.cover 2 3 4 5))
private theorem t9_75OK : treeOK shape9_5 32769 66 t9_75=true := by decide

private def t9_69 : Tree 9 := .split 15 t9_70 t9_75
private theorem t9_69OK : treeOK shape9_5 1 66 t9_69=true := by
  change (treeOK shape9_5 1 (66 ||| 2^15) t9_70 && treeOK shape9_5 (1 ||| 2^15) 66 t9_75)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_70OK,t9_75OK⟩

private def t9_76 : Tree 9 := (.split 7 (.split 20 (.split 3 (.split 12 (.tip (.cover 1 2 4 6)) (.split 8 (.split 11 (.tip (.cover 1 3 4 5)) (.tip (.cover 1 2 5 6))) (.tip (.cover 1 2 4 6)))) (.split 8 (.split 15 (.tip (.cover 1 3 5 6)) (.tip (.cover 0 1 3 6))) (.tip (.cover 1 2 4 6)))) (.tip (.cover 0 2 4 7))) (.tip (.cover 1 2 4 5)))
private theorem t9_76OK : treeOK shape9_5 65 2 t9_76=true := by decide

private def t9_68 : Tree 9 := .split 6 t9_69 t9_76
private theorem t9_68OK : treeOK shape9_5 1 2 t9_68=true := by
  change (treeOK shape9_5 1 (2 ||| 2^6) t9_69 && treeOK shape9_5 (1 ||| 2^6) 2 t9_76)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_69OK,t9_76OK⟩

private def t9_78 : Tree 9 := (.split 2 (.split 20 (.split 3 (.split 15 (.tip (.cover 1 2 5 6)) (.tip (.cover 1 3 4 5))) (.tip (.cover 1 3 4 6))) (.tip (.cover 0 3 4 7))) (.tip (.cover 1 3 4 5)))
private theorem t9_78OK : treeOK shape9_5 3 64 t9_78=true := by decide

private def t9_79 : Tree 9 := (.split 2 (.split 8 (.split 13 (.split 5 (.split 7 (.tip (.cover 1 2 3 5)) (.tip (.cover 1 2 4 5))) (.tip (.cover 0 3 4 8))) (.tip (.cover 0 2 3 7))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t9_79OK : treeOK shape9_5 67 0 t9_79=true := by decide

private def t9_77 : Tree 9 := .split 6 t9_78 t9_79
private theorem t9_77OK : treeOK shape9_5 3 0 t9_77=true := by
  change (treeOK shape9_5 3 (0 ||| 2^6) t9_78 && treeOK shape9_5 (3 ||| 2^6) 0 t9_79)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_78OK,t9_79OK⟩

private def t9_67 : Tree 9 := .split 1 t9_68 t9_77
private theorem t9_67OK : treeOK shape9_5 1 0 t9_67=true := by
  change (treeOK shape9_5 1 (0 ||| 2^1) t9_68 && treeOK shape9_5 (1 ||| 2^1) 0 t9_77)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_68OK,t9_77OK⟩

private def t9_49 : Tree 9 := .split 0 t9_50 t9_67
private theorem t9_49OK : treeOK shape9_5 0 0 t9_49=true := by
  change (treeOK shape9_5 0 (0 ||| 2^0) t9_50 && treeOK shape9_5 (0 ||| 2^0) 0 t9_67)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_50OK,t9_67OK⟩

private def shape9_6 : Shape := ⟨false,6,4,3⟩
private def t9_81 : Tree 9 := (.split 1 (.tip (.small 1)) (.split 6 (.tip (.small 1)) (.split 11 (.split 18 (.split 5 (.tip (.small 1)) (.split 10 (.tip (.small 1)) (.tip (.cover 0 1 2 3)))) (.tip (.cover 1 2 3 6))) (.tip (.cover 1 2 3 5)))))
private theorem t9_81OK : treeOK shape9_6 0 1 t9_81=true := by decide

private def t9_83 : Tree 9 := (.split 6 (.tip (.small 1)) (.split 7 (.split 18 (.split 5 (.tip (.small 1)) (.split 10 (.tip (.small 1)) (.tip (.cover 0 2 4 8)))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 2 4 5))))
private theorem t9_83OK : treeOK shape9_6 1 2 t9_83=true := by decide

private def t9_85 : Tree 9 := (.split 2 (.split 18 (.split 5 (.tip (.small 1)) (.tip (.cover 0 3 4 8))) (.tip (.cover 1 3 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t9_85OK : treeOK shape9_6 3 64 t9_85=true := by decide

private def t9_86 : Tree 9 := (.split 2 (.split 8 (.split 13 (.split 5 (.split 7 (.tip (.cover 1 2 3 5)) (.tip (.cover 1 2 4 5))) (.tip (.cover 0 3 4 8))) (.tip (.cover 1 2 3 7))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t9_86OK : treeOK shape9_6 67 0 t9_86=true := by decide

private def t9_84 : Tree 9 := .split 6 t9_85 t9_86
private theorem t9_84OK : treeOK shape9_6 3 0 t9_84=true := by
  change (treeOK shape9_6 3 (0 ||| 2^6) t9_85 && treeOK shape9_6 (3 ||| 2^6) 0 t9_86)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_85OK,t9_86OK⟩

private def t9_82 : Tree 9 := .split 1 t9_83 t9_84
private theorem t9_82OK : treeOK shape9_6 1 0 t9_82=true := by
  change (treeOK shape9_6 1 (0 ||| 2^1) t9_83 && treeOK shape9_6 (1 ||| 2^1) 0 t9_84)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_83OK,t9_84OK⟩

private def t9_80 : Tree 9 := .split 0 t9_81 t9_82
private theorem t9_80OK : treeOK shape9_6 0 0 t9_80=true := by
  change (treeOK shape9_6 0 (0 ||| 2^0) t9_81 && treeOK shape9_6 (0 ||| 2^0) 0 t9_82)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_81OK,t9_82OK⟩

private def shape9_7 : Shape := ⟨true,4,4,0⟩
private def t9_87 : Tree 9 := (.tip (.small 0))
private theorem t9_87OK : treeOK shape9_7 0 0 t9_87=true := by decide

private def shape9_8 : Shape := ⟨true,5,4,0⟩
private def t9_88 : Tree 9 := (.tip (.small 1))
private theorem t9_88OK : treeOK shape9_8 0 0 t9_88=true := by decide

private def shape9_9 : Shape := ⟨true,4,4,1⟩
private def t9_89 : Tree 9 := (.tip (.small 0))
private theorem t9_89OK : treeOK shape9_9 0 0 t9_89=true := by decide

private def shape9_10 : Shape := ⟨true,5,4,1⟩
private def t9_90 : Tree 9 := (.tip (.small 1))
private theorem t9_90OK : treeOK shape9_10 0 0 t9_90=true := by decide

private def shape9_11 : Shape := ⟨true,5,5,1⟩
private def t9_95 : Tree 9 := (.split 6 (.tip (.small 0)) (.split 7 (.tip (.small 0)) (.split 10 (.split 1 (.tip (.small 0)) (.tip (.cover 0 2 3 8))) (.tip (.cover 2 4 5 8)))))
private theorem t9_95OK : treeOK shape9_11 0 264225 t9_95=true := by decide

private def t9_96 : Tree 9 := (.split 19 (.split 20 (.tip (.small 1)) (.split 1 (.tip (.small 0)) (.split 2 (.tip (.small 0)) (.tip (.cover 1 4 5 8))))) (.split 20 (.split 1 (.tip (.small 0)) (.split 2 (.tip (.small 0)) (.tip (.cover 1 4 5 8)))) (.tip (.cover 0 2 6 7))))
private theorem t9_96OK : treeOK shape9_11 32 264193 t9_96=true := by decide

private def t9_94 : Tree 9 := .split 5 t9_95 t9_96
private theorem t9_94OK : treeOK shape9_11 0 264193 t9_94=true := by
  change (treeOK shape9_11 0 (264193 ||| 2^5) t9_95 && treeOK shape9_11 (0 ||| 2^5) 264193 t9_96)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_95OK,t9_96OK⟩

private def t9_98 : Tree 9 := (.split 4 (.split 6 (.tip (.small 0)) (.split 7 (.tip (.small 0)) (.tip (.cover 2 4 5 6)))) (.split 20 (.split 1 (.tip (.small 0)) (.split 2 (.tip (.small 0)) (.tip (.cover 1 4 5 7)))) (.tip (.cover 0 2 6 8))))
private theorem t9_98OK : treeOK shape9_11 262144 526337 t9_98=true := by decide

private def t9_99 : Tree 9 := (.split 20 (.split 3 (.split 6 (.tip (.small 0)) (.tip (.cover 2 3 7 8))) (.tip (.cover 0 2 7 8))) (.split 3 (.split 4 (.split 6 (.tip (.small 0)) (.tip (.cover 2 3 6 7))) (.tip (.cover 0 2 6 8))) (.tip (.cover 0 2 7 8))))
private theorem t9_99OK : treeOK shape9_11 786432 2049 t9_99=true := by decide

private def t9_97 : Tree 9 := .split 19 t9_98 t9_99
private theorem t9_97OK : treeOK shape9_11 262144 2049 t9_97=true := by
  change (treeOK shape9_11 262144 (2049 ||| 2^19) t9_98 && treeOK shape9_11 (262144 ||| 2^19) 2049 t9_99)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_98OK,t9_99OK⟩

private def t9_93 : Tree 9 := .split 18 t9_94 t9_97
private theorem t9_93OK : treeOK shape9_11 0 2049 t9_93=true := by
  change (treeOK shape9_11 0 (2049 ||| 2^18) t9_94 && treeOK shape9_11 (0 ||| 2^18) 2049 t9_97)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_94OK,t9_97OK⟩

private def t9_102 : Tree 9 := (.split 6 (.tip (.small 0)) (.split 7 (.tip (.small 0)) (.split 17 (.split 19 (.split 20 (.tip (.small 1)) (.tip (.cover 2 3 4 7))) (.tip (.cover 2 3 4 6))) (.tip (.cover 2 3 4 8)))))
private theorem t9_102OK : treeOK shape9_11 2048 262147 t9_102=true := by decide

private def t9_103 : Tree 9 := (.split 2 (.split 6 (.tip (.small 0)) (.tip (.cover 1 2 3 5))) (.split 5 (.split 6 (.tip (.cover 1 2 3 4)) (.tip (.cover 1 2 3 5))) (.split 6 (.tip (.cover 1 2 3 4)) (.tip (.cover 0 1 2 4)))))
private theorem t9_103OK : treeOK shape9_11 2050 262145 t9_103=true := by decide

private def t9_101 : Tree 9 := .split 1 t9_102 t9_103
private theorem t9_101OK : treeOK shape9_11 2048 262145 t9_101=true := by
  change (treeOK shape9_11 2048 (262145 ||| 2^1) t9_102 && treeOK shape9_11 (2048 ||| 2^1) 262145 t9_103)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_102OK,t9_103OK⟩

private def t9_104 : Tree 9 := (.split 19 (.split 1 (.split 6 (.tip (.small 0)) (.tip (.cover 2 3 5 6))) (.split 2 (.split 6 (.tip (.small 0)) (.tip (.cover 1 2 3 5))) (.split 4 (.split 6 (.tip (.cover 1 2 3 4)) (.tip (.cover 0 2 4 6))) (.tip (.cover 0 1 4 7))))) (.tip (.cover 2 4 7 8)))
private theorem t9_104OK : treeOK shape9_11 264192 1 t9_104=true := by decide

private def t9_100 : Tree 9 := .split 18 t9_101 t9_104
private theorem t9_100OK : treeOK shape9_11 2048 1 t9_100=true := by
  change (treeOK shape9_11 2048 (1 ||| 2^18) t9_101 && treeOK shape9_11 (2048 ||| 2^18) 1 t9_104)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_101OK,t9_104OK⟩

private def t9_92 : Tree 9 := .split 11 t9_93 t9_100
private theorem t9_92OK : treeOK shape9_11 0 1 t9_92=true := by
  change (treeOK shape9_11 0 (1 ||| 2^11) t9_93 && treeOK shape9_11 (0 ||| 2^11) 1 t9_100)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_93OK,t9_100OK⟩

private def t9_109 : Tree 9 := (.split 6 (.tip (.small 0)) (.split 11 (.tip (.small 0)) (.split 14 (.tip (.cover 0 2 4 8)) (.tip (.cover 2 3 5 8)))))
private theorem t9_109OK : treeOK shape9_11 1 262306 t9_109=true := by decide

private def t9_110 : Tree 9 := (.split 19 (.split 20 (.tip (.small 1)) (.split 2 (.tip (.small 0)) (.tip (.cover 1 3 5 8)))) (.split 20 (.split 2 (.tip (.small 0)) (.tip (.cover 1 3 5 8))) (.tip (.cover 0 2 6 7))))
private theorem t9_110OK : treeOK shape9_11 33 262274 t9_110=true := by decide

private def t9_108 : Tree 9 := .split 5 t9_109 t9_110
private theorem t9_108OK : treeOK shape9_11 1 262274 t9_108=true := by
  change (treeOK shape9_11 1 (262274 ||| 2^5) t9_109 && treeOK shape9_11 (1 ||| 2^5) 262274 t9_110)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_109OK,t9_110OK⟩

private def t9_111 : Tree 9 := (.split 19 (.split 4 (.split 6 (.tip (.small 0)) (.split 11 (.tip (.small 0)) (.tip (.cover 0 2 4 6)))) (.split 20 (.split 2 (.tip (.small 0)) (.tip (.cover 1 3 5 7))) (.tip (.cover 0 2 6 8)))) (.tip (.cover 0 2 7 8)))
private theorem t9_111OK : treeOK shape9_11 262145 130 t9_111=true := by decide

private def t9_107 : Tree 9 := .split 18 t9_108 t9_111
private theorem t9_107OK : treeOK shape9_11 1 130 t9_107=true := by
  change (treeOK shape9_11 1 (130 ||| 2^18) t9_108 && treeOK shape9_11 (1 ||| 2^18) 130 t9_111)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_108OK,t9_111OK⟩

private def t9_113 : Tree 9 := (.split 2 (.split 6 (.tip (.small 0)) (.tip (.cover 1 2 4 5))) (.split 5 (.split 6 (.tip (.cover 1 2 3 4)) (.tip (.cover 1 2 4 5))) (.split 6 (.tip (.cover 1 2 3 4)) (.tip (.cover 0 1 2 3)))))
private theorem t9_113OK : treeOK shape9_11 129 262146 t9_113=true := by decide

private def t9_114 : Tree 9 := (.split 19 (.split 2 (.split 6 (.tip (.small 0)) (.tip (.cover 1 2 4 5))) (.split 4 (.split 6 (.tip (.cover 1 2 3 4)) (.tip (.cover 0 2 3 6))) (.tip (.cover 0 1 3 7)))) (.tip (.cover 0 1 3 6)))
private theorem t9_114OK : treeOK shape9_11 262273 2 t9_114=true := by decide

private def t9_112 : Tree 9 := .split 18 t9_113 t9_114
private theorem t9_112OK : treeOK shape9_11 129 2 t9_112=true := by
  change (treeOK shape9_11 129 (2 ||| 2^18) t9_113 && treeOK shape9_11 (129 ||| 2^18) 2 t9_114)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_113OK,t9_114OK⟩

private def t9_106 : Tree 9 := .split 7 t9_107 t9_112
private theorem t9_106OK : treeOK shape9_11 1 2 t9_106=true := by
  change (treeOK shape9_11 1 (2 ||| 2^7) t9_107 && treeOK shape9_11 (1 ||| 2^7) 2 t9_112)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_107OK,t9_112OK⟩

private def t9_118 : Tree 9 := (.split 5 (.split 7 (.tip (.small 0)) (.split 11 (.tip (.small 0)) (.tip (.cover 0 1 2 5)))) (.split 19 (.split 20 (.tip (.small 1)) (.tip (.cover 1 3 4 8))) (.tip (.cover 1 3 4 8))))
private theorem t9_118OK : treeOK shape9_11 3 262212 t9_118=true := by decide

private def t9_119 : Tree 9 := (.split 19 (.split 4 (.split 7 (.tip (.small 0)) (.split 11 (.tip (.small 0)) (.tip (.cover 0 1 2 5)))) (.tip (.cover 1 3 4 7))) (.tip (.cover 0 1 2 6)))
private theorem t9_119OK : treeOK shape9_11 262147 68 t9_119=true := by decide

private def t9_117 : Tree 9 := .split 18 t9_118 t9_119
private theorem t9_117OK : treeOK shape9_11 3 68 t9_117=true := by
  change (treeOK shape9_11 3 (68 ||| 2^18) t9_118 && treeOK shape9_11 (3 ||| 2^18) 68 t9_119)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_118OK,t9_119OK⟩

private def t9_120 : Tree 9 := (.split 18 (.split 5 (.split 7 (.tip (.cover 1 2 3 5)) (.tip (.cover 1 2 4 5))) (.split 7 (.tip (.cover 1 2 3 5)) (.tip (.cover 0 1 2 3)))) (.split 19 (.split 4 (.split 7 (.tip (.cover 1 2 3 5)) (.tip (.cover 0 2 3 6))) (.tip (.cover 0 1 3 7))) (.tip (.cover 0 1 2 6))))
private theorem t9_120OK : treeOK shape9_11 67 4 t9_120=true := by decide

private def t9_116 : Tree 9 := .split 6 t9_117 t9_120
private theorem t9_116OK : treeOK shape9_11 3 4 t9_116=true := by
  change (treeOK shape9_11 3 (4 ||| 2^6) t9_117 && treeOK shape9_11 (3 ||| 2^6) 4 t9_120)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_117OK,t9_120OK⟩

private def t9_121 : Tree 9 := (.tip (.cover 1 3 4 5))
private theorem t9_121OK : treeOK shape9_11 7 0 t9_121=true := by decide

private def t9_115 : Tree 9 := .split 2 t9_116 t9_121
private theorem t9_115OK : treeOK shape9_11 3 0 t9_115=true := by
  change (treeOK shape9_11 3 (0 ||| 2^2) t9_116 && treeOK shape9_11 (3 ||| 2^2) 0 t9_121)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_116OK,t9_121OK⟩

private def t9_105 : Tree 9 := .split 1 t9_106 t9_115
private theorem t9_105OK : treeOK shape9_11 1 0 t9_105=true := by
  change (treeOK shape9_11 1 (0 ||| 2^1) t9_106 && treeOK shape9_11 (1 ||| 2^1) 0 t9_115)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_106OK,t9_115OK⟩

private def t9_91 : Tree 9 := .split 0 t9_92 t9_105
private theorem t9_91OK : treeOK shape9_11 0 0 t9_91=true := by
  change (treeOK shape9_11 0 (0 ||| 2^0) t9_92 && treeOK shape9_11 (0 ||| 2^0) 0 t9_105)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_92OK,t9_105OK⟩

private def shape9_12 : Shape := ⟨true,6,4,1⟩
private def t9_122 : Tree 9 := (.tip (.small 1))
private theorem t9_122OK : treeOK shape9_12 0 0 t9_122=true := by decide

private def shape9_13 : Shape := ⟨true,4,4,2⟩
private def t9_123 : Tree 9 := (.split 0 (.tip (.small 0)) (.split 1 (.tip (.small 0)) (.split 2 (.tip (.small 1)) (.split 6 (.tip (.small 0)) (.split 7 (.tip (.small 1)) (.tip (.cover 0 1 4 5)))))))
private theorem t9_123OK : treeOK shape9_13 0 0 t9_123=true := by decide

private def shape9_14 : Shape := ⟨true,5,4,2⟩
private def t9_125 : Tree 9 := (.tip (.small 1))
private theorem t9_125OK : treeOK shape9_14 0 1 t9_125=true := by decide

private def t9_128 : Tree 9 := (.split 3 (.tip (.small 1)) (.split 8 (.tip (.small 1)) (.split 18 (.tip (.cover 0 1 6 7)) (.split 19 (.tip (.cover 0 1 6 8)) (.split 20 (.tip (.cover 0 1 7 8)) (.tip (.cover 0 1 2 7)))))))
private theorem t9_128OK : treeOK shape9_14 1 130 t9_128=true := by decide

private def t9_129 : Tree 9 := (.split 8 (.tip (.small 1)) (.split 2 (.split 6 (.split 18 (.split 10 (.tip (.cover 0 1 3 8)) (.split 11 (.tip (.small 0)) (.tip (.cover 0 2 5 6)))) (.tip (.cover 1 2 5 6))) (.tip (.cover 1 2 4 5))) (.split 3 (.tip (.small 1)) (.tip (.cover 0 1 5 6)))))
private theorem t9_129OK : treeOK shape9_14 129 2 t9_129=true := by decide

private def t9_127 : Tree 9 := .split 7 t9_128 t9_129
private theorem t9_127OK : treeOK shape9_14 1 2 t9_127=true := by
  change (treeOK shape9_14 1 (2 ||| 2^7) t9_128 && treeOK shape9_14 (1 ||| 2^7) 2 t9_129)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_128OK,t9_129OK⟩

private def t9_130 : Tree 9 := (.split 2 (.split 6 (.split 3 (.tip (.small 1)) (.split 8 (.tip (.small 1)) (.split 18 (.tip (.cover 0 1 6 7)) (.tip (.cover 1 3 4 6))))) (.split 8 (.tip (.small 1)) (.split 3 (.tip (.small 1)) (.tip (.cover 0 1 4 6))))) (.tip (.cover 1 3 4 5)))
private theorem t9_130OK : treeOK shape9_14 3 0 t9_130=true := by decide

private def t9_126 : Tree 9 := .split 1 t9_127 t9_130
private theorem t9_126OK : treeOK shape9_14 1 0 t9_126=true := by
  change (treeOK shape9_14 1 (0 ||| 2^1) t9_127 && treeOK shape9_14 (1 ||| 2^1) 0 t9_130)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_127OK,t9_130OK⟩

private def t9_124 : Tree 9 := .split 0 t9_125 t9_126
private theorem t9_124OK : treeOK shape9_14 0 0 t9_124=true := by
  change (treeOK shape9_14 0 (0 ||| 2^0) t9_125 && treeOK shape9_14 (0 ||| 2^0) 0 t9_126)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_125OK,t9_126OK⟩

private def shape9_15 : Shape := ⟨true,5,5,2⟩
private def t9_135 : Tree 9 := (.split 2 (.tip (.small 0)) (.split 6 (.tip (.small 0)) (.split 7 (.tip (.small 0)) (.split 8 (.split 9 (.tip (.small 1)) (.tip (.cover 2 4 5 7))) (.tip (.cover 2 4 5 6))))))
private theorem t9_135OK : treeOK shape9_15 0 264195 t9_135=true := by decide

private def t9_136 : Tree 9 := (.split 2 (.split 6 (.tip (.small 0)) (.split 7 (.tip (.small 0)) (.split 8 (.split 9 (.tip (.small 1)) (.tip (.cover 2 4 5 7))) (.tip (.cover 2 4 5 6))))) (.split 3 (.split 4 (.tip (.small 1)) (.tip (.cover 3 4 5 7))) (.tip (.cover 3 4 5 6))))
private theorem t9_136OK : treeOK shape9_15 2 264193 t9_136=true := by decide

private def t9_134 : Tree 9 := .split 1 t9_135 t9_136
private theorem t9_134OK : treeOK shape9_15 0 264193 t9_134=true := by
  change (treeOK shape9_15 0 (264193 ||| 2^1) t9_135 && treeOK shape9_15 (0 ||| 2^1) 264193 t9_136)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_135OK,t9_136OK⟩

private def t9_139 : Tree 9 := (.split 20 (.split 1 (.split 2 (.tip (.small 0)) (.split 6 (.tip (.small 0)) (.tip (.cover 0 2 3 6)))) (.split 2 (.split 6 (.tip (.small 0)) (.tip (.cover 0 2 3 6))) (.tip (.cover 3 4 5 6)))) (.split 4 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.cover 0 2 3 6)))))
private theorem t9_139OK : treeOK shape9_15 262144 2313 t9_139=true := by decide

private def t9_140 : Tree 9 := (.split 9 (.split 4 (.tip (.small 1)) (.split 14 (.split 17 (.tip (.cover 1 4 5 8)) (.tip (.cover 1 2 3 5))) (.tip (.cover 1 2 3 4)))) (.split 20 (.tip (.cover 0 1 7 8)) (.split 4 (.split 6 (.split 7 (.tip (.small 0)) (.tip (.cover 0 1 3 7))) (.tip (.cover 0 1 3 7))) (.tip (.cover 0 2 3 6)))))
private theorem t9_140OK : treeOK shape9_15 262400 2057 t9_140=true := by decide

private def t9_138 : Tree 9 := .split 8 t9_139 t9_140
private theorem t9_138OK : treeOK shape9_15 262144 2057 t9_138=true := by
  change (treeOK shape9_15 262144 (2057 ||| 2^8) t9_139 && treeOK shape9_15 (262144 ||| 2^8) 2057 t9_140)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_139OK,t9_140OK⟩

private def t9_142 : Tree 9 := (.split 8 (.split 9 (.tip (.small 1)) (.split 14 (.split 17 (.tip (.cover 1 4 5 8)) (.tip (.cover 1 2 3 5))) (.tip (.cover 1 2 3 4)))) (.tip (.cover 0 2 3 7)))
private theorem t9_142OK : treeOK shape9_15 262152 2065 t9_142=true := by decide

private def t9_143 : Tree 9 := (.split 8 (.split 20 (.tip (.cover 0 1 7 8)) (.split 1 (.split 2 (.tip (.small 0)) (.tip (.cover 0 1 2 7))) (.tip (.cover 0 1 2 7)))) (.tip (.cover 0 2 3 7)))
private theorem t9_143OK : treeOK shape9_15 262168 2049 t9_143=true := by decide

private def t9_141 : Tree 9 := .split 4 t9_142 t9_143
private theorem t9_141OK : treeOK shape9_15 262152 2049 t9_141=true := by
  change (treeOK shape9_15 262152 (2049 ||| 2^4) t9_142 && treeOK shape9_15 (262152 ||| 2^4) 2049 t9_143)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_142OK,t9_143OK⟩

private def t9_137 : Tree 9 := .split 3 t9_138 t9_141
private theorem t9_137OK : treeOK shape9_15 262144 2049 t9_137=true := by
  change (treeOK shape9_15 262144 (2049 ||| 2^3) t9_138 && treeOK shape9_15 (262144 ||| 2^3) 2049 t9_141)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_138OK,t9_141OK⟩

private def t9_133 : Tree 9 := .split 18 t9_134 t9_137
private theorem t9_133OK : treeOK shape9_15 0 2049 t9_133=true := by
  change (treeOK shape9_15 0 (2049 ||| 2^18) t9_134 && treeOK shape9_15 (0 ||| 2^18) 2049 t9_137)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_134OK,t9_137OK⟩

private def t9_147 : Tree 9 := (.split 17 (.split 2 (.tip (.small 0)) (.tip (.cover 0 1 5 8))) (.split 2 (.tip (.small 0)) (.split 7 (.tip (.small 0)) (.tip (.cover 1 2 3 4)))))
private theorem t9_147OK : treeOK shape9_15 2048 262211 t9_147=true := by decide

private def t9_148 : Tree 9 := (.split 7 (.split 2 (.tip (.small 0)) (.split 14 (.tip (.cover 0 1 4 8)) (.split 17 (.tip (.cover 0 1 5 8)) (.tip (.cover 0 1 4 5))))) (.split 17 (.tip (.cover 0 1 5 8)) (.split 2 (.split 8 (.split 9 (.tip (.small 1)) (.tip (.cover 0 1 3 5))) (.tip (.cover 0 1 3 5))) (.tip (.cover 1 2 3 4)))))
private theorem t9_148OK : treeOK shape9_15 2112 262147 t9_148=true := by decide

private def t9_146 : Tree 9 := .split 6 t9_147 t9_148
private theorem t9_146OK : treeOK shape9_15 2048 262147 t9_146=true := by
  change (treeOK shape9_15 2048 (262147 ||| 2^6) t9_147 && treeOK shape9_15 (2048 ||| 2^6) 262147 t9_148)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_147OK,t9_148OK⟩

private def t9_150 : Tree 9 := (.split 6 (.split 7 (.tip (.small 0)) (.split 14 (.tip (.cover 0 1 4 8)) (.split 17 (.tip (.cover 0 1 5 8)) (.tip (.cover 0 1 4 5))))) (.tip (.cover 1 2 3 5)))
private theorem t9_150OK : treeOK shape9_15 2050 262149 t9_150=true := by decide

private def t9_151 : Tree 9 := (.split 6 (.split 17 (.tip (.cover 0 1 5 8)) (.split 3 (.split 4 (.tip (.small 1)) (.tip (.cover 0 1 2 5))) (.tip (.cover 0 1 2 5)))) (.tip (.cover 1 2 3 5)))
private theorem t9_151OK : treeOK shape9_15 2054 262145 t9_151=true := by decide

private def t9_149 : Tree 9 := .split 2 t9_150 t9_151
private theorem t9_149OK : treeOK shape9_15 2050 262145 t9_149=true := by
  change (treeOK shape9_15 2050 (262145 ||| 2^2) t9_150 && treeOK shape9_15 (2050 ||| 2^2) 262145 t9_151)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_150OK,t9_151OK⟩

private def t9_145 : Tree 9 := .split 1 t9_146 t9_149
private theorem t9_145OK : treeOK shape9_15 2048 262145 t9_145=true := by
  change (treeOK shape9_15 2048 (262145 ||| 2^1) t9_146 && treeOK shape9_15 (2048 ||| 2^1) 262145 t9_149)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_146OK,t9_149OK⟩

private def t9_152 : Tree 9 := (.tip (.cover 2 3 4 6))
private theorem t9_152OK : treeOK shape9_15 264192 1 t9_152=true := by decide

private def t9_144 : Tree 9 := .split 18 t9_145 t9_152
private theorem t9_144OK : treeOK shape9_15 2048 1 t9_144=true := by
  change (treeOK shape9_15 2048 (1 ||| 2^18) t9_145 && treeOK shape9_15 (2048 ||| 2^18) 1 t9_152)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_145OK,t9_152OK⟩

private def t9_132 : Tree 9 := .split 11 t9_133 t9_144
private theorem t9_132OK : treeOK shape9_15 0 1 t9_132=true := by
  change (treeOK shape9_15 0 (1 ||| 2^11) t9_133 && treeOK shape9_15 (0 ||| 2^11) 1 t9_144)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_133OK,t9_144OK⟩

private def t9_157 : Tree 9 := (.split 6 (.tip (.small 0)) (.split 8 (.split 9 (.tip (.cover 0 3 6 7)) (.split 11 (.tip (.small 0)) (.tip (.cover 0 2 4 7)))) (.split 9 (.split 11 (.tip (.small 0)) (.tip (.cover 0 2 4 6))) (.tip (.cover 0 2 6 7)))))
private theorem t9_157OK : treeOK shape9_15 1 262278 t9_157=true := by decide

private def t9_159 : Tree 9 := (.split 4 (.tip (.cover 0 2 6 7)) (.split 6 (.split 11 (.tip (.small 0)) (.tip (.cover 0 3 5 7))) (.split 9 (.split 11 (.split 5 (.tip (.cover 0 1 2 8)) (.split 8 (.tip (.small 1)) (.tip (.cover 0 1 2 3)))) (.tip (.cover 0 1 2 4))) (.tip (.cover 0 1 2 3)))))
private theorem t9_159OK : treeOK shape9_15 5 262282 t9_159=true := by decide

private def t9_160 : Tree 9 := (.split 4 (.split 6 (.split 11 (.tip (.small 0)) (.tip (.cover 0 3 5 6))) (.split 8 (.split 11 (.split 5 (.tip (.cover 0 1 2 8)) (.split 9 (.tip (.small 1)) (.tip (.cover 0 1 2 3)))) (.tip (.cover 0 1 2 4))) (.tip (.cover 0 1 2 3)))) (.tip (.cover 0 3 6 7)))
private theorem t9_160OK : treeOK shape9_15 13 262274 t9_160=true := by decide

private def t9_158 : Tree 9 := .split 3 t9_159 t9_160
private theorem t9_158OK : treeOK shape9_15 5 262274 t9_158=true := by
  change (treeOK shape9_15 5 (262274 ||| 2^3) t9_159 && treeOK shape9_15 (5 ||| 2^3) 262274 t9_160)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_159OK,t9_160OK⟩

private def t9_156 : Tree 9 := .split 2 t9_157 t9_158
private theorem t9_156OK : treeOK shape9_15 1 262274 t9_156=true := by
  change (treeOK shape9_15 1 (262274 ||| 2^2) t9_157 && treeOK shape9_15 (1 ||| 2^2) 262274 t9_158)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_157OK,t9_158OK⟩

private def t9_163 : Tree 9 := (.split 11 (.split 19 (.split 2 (.tip (.small 0)) (.split 4 (.split 6 (.tip (.small 0)) (.tip (.cover 0 2 3 6))) (.tip (.cover 1 3 5 7)))) (.split 20 (.split 2 (.tip (.small 0)) (.tip (.cover 0 1 2 6))) (.tip (.cover 0 2 6 7)))) (.tip (.cover 2 3 4 6)))
private theorem t9_163OK : treeOK shape9_15 262145 650 t9_163=true := by decide

private def t9_164 : Tree 9 := (.split 20 (.tip (.cover 0 1 7 8)) (.split 4 (.split 6 (.split 11 (.tip (.small 0)) (.tip (.cover 1 2 4 7))) (.tip (.cover 0 1 3 7))) (.tip (.cover 0 2 3 6))))
private theorem t9_164OK : treeOK shape9_15 262657 138 t9_164=true := by decide

private def t9_162 : Tree 9 := .split 9 t9_163 t9_164
private theorem t9_162OK : treeOK shape9_15 262145 138 t9_162=true := by
  change (treeOK shape9_15 262145 (138 ||| 2^9) t9_163 && treeOK shape9_15 (262145 ||| 2^9) 138 t9_164)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_163OK,t9_164OK⟩

private def t9_165 : Tree 9 := (.split 4 (.split 8 (.split 11 (.split 19 (.tip (.cover 0 1 6 8)) (.split 20 (.split 2 (.tip (.small 0)) (.tip (.cover 0 1 2 6))) (.tip (.cover 0 1 2 7)))) (.tip (.cover 1 3 4 6))) (.tip (.cover 0 2 3 7))) (.tip (.cover 0 3 6 7)))
private theorem t9_165OK : treeOK shape9_15 262153 130 t9_165=true := by decide

private def t9_161 : Tree 9 := .split 3 t9_162 t9_165
private theorem t9_161OK : treeOK shape9_15 262145 130 t9_161=true := by
  change (treeOK shape9_15 262145 (130 ||| 2^3) t9_162 && treeOK shape9_15 (262145 ||| 2^3) 130 t9_165)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_162OK,t9_165OK⟩

private def t9_155 : Tree 9 := .split 18 t9_156 t9_161
private theorem t9_155OK : treeOK shape9_15 1 130 t9_155=true := by
  change (treeOK shape9_15 1 (130 ||| 2^18) t9_156 && treeOK shape9_15 (1 ||| 2^18) 130 t9_161)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_156OK,t9_161OK⟩

private def t9_168 : Tree 9 := (.split 9 (.split 11 (.tip (.cover 1 2 4 5)) (.split 18 (.tip (.cover 0 3 6 7)) (.tip (.cover 0 2 5 6)))) (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 2 5 7))))
private theorem t9_168OK : treeOK shape9_15 129 262 t9_168=true := by decide

private def t9_169 : Tree 9 := (.split 4 (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 2 3 4))) (.split 9 (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 1 2 5))) (.tip (.cover 0 1 2 3))))
private theorem t9_169OK : treeOK shape9_15 133 258 t9_169=true := by decide

private def t9_167 : Tree 9 := .split 2 t9_168 t9_169
private theorem t9_167OK : treeOK shape9_15 129 258 t9_167=true := by
  change (treeOK shape9_15 129 (258 ||| 2^2) t9_168 && treeOK shape9_15 (129 ||| 2^2) 258 t9_169)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_168OK,t9_169OK⟩

private def t9_170 : Tree 9 := (.split 9 (.split 2 (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 2 5 6))) (.split 3 (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 1 3 5))) (.tip (.cover 0 1 2 3)))) (.tip (.cover 0 2 6 7)))
private theorem t9_170OK : treeOK shape9_15 385 2 t9_170=true := by decide

private def t9_166 : Tree 9 := .split 8 t9_167 t9_170
private theorem t9_166OK : treeOK shape9_15 129 2 t9_166=true := by
  change (treeOK shape9_15 129 (2 ||| 2^8) t9_167 && treeOK shape9_15 (129 ||| 2^8) 2 t9_170)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_167OK,t9_170OK⟩

private def t9_154 : Tree 9 := .split 7 t9_155 t9_166
private theorem t9_154OK : treeOK shape9_15 1 2 t9_154=true := by
  change (treeOK shape9_15 1 (2 ||| 2^7) t9_155 && treeOK shape9_15 (1 ||| 2^7) 2 t9_166)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_155OK,t9_166OK⟩

private def t9_175 : Tree 9 := (.split 4 (.tip (.cover 0 2 6 7)) (.split 7 (.split 11 (.tip (.small 0)) (.tip (.cover 0 3 4 7))) (.split 9 (.split 11 (.split 5 (.tip (.cover 0 1 2 8)) (.split 8 (.tip (.small 1)) (.tip (.cover 0 1 2 3)))) (.tip (.cover 0 1 2 5))) (.tip (.cover 0 1 2 3)))))
private theorem t9_175OK : treeOK shape9_15 3 262220 t9_175=true := by decide

private def t9_176 : Tree 9 := (.split 4 (.split 7 (.split 11 (.tip (.small 0)) (.tip (.cover 0 3 4 6))) (.split 8 (.split 11 (.split 5 (.tip (.cover 0 1 2 8)) (.split 9 (.tip (.small 1)) (.tip (.cover 0 1 2 3)))) (.tip (.cover 0 1 2 5))) (.tip (.cover 0 1 2 3)))) (.tip (.cover 0 3 6 7)))
private theorem t9_176OK : treeOK shape9_15 11 262212 t9_176=true := by decide

private def t9_174 : Tree 9 := .split 3 t9_175 t9_176
private theorem t9_174OK : treeOK shape9_15 3 262212 t9_174=true := by
  change (treeOK shape9_15 3 (262212 ||| 2^3) t9_175 && treeOK shape9_15 (3 ||| 2^3) 262212 t9_176)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_175OK,t9_176OK⟩

private def t9_177 : Tree 9 := (.split 3 (.split 9 (.split 11 (.split 19 (.split 4 (.split 7 (.tip (.small 0)) (.tip (.cover 0 2 3 6))) (.tip (.cover 1 3 4 7))) (.tip (.cover 0 1 2 6))) (.tip (.cover 0 3 4 6))) (.tip (.cover 0 1 2 7))) (.tip (.cover 1 3 4 6)))
private theorem t9_177OK : treeOK shape9_15 262147 68 t9_177=true := by decide

private def t9_173 : Tree 9 := .split 18 t9_174 t9_177
private theorem t9_173OK : treeOK shape9_15 3 68 t9_173=true := by
  change (treeOK shape9_15 3 (68 ||| 2^18) t9_174 && treeOK shape9_15 (3 ||| 2^18) 68 t9_177)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_174OK,t9_177OK⟩

private def t9_178 : Tree 9 := (.split 8 (.split 4 (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 2 3 5))) (.split 9 (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 1 2 4))) (.tip (.cover 0 1 2 3)))) (.split 9 (.split 3 (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 1 3 4))) (.tip (.cover 0 1 2 3))) (.tip (.cover 0 2 6 7))))
private theorem t9_178OK : treeOK shape9_15 67 4 t9_178=true := by decide

private def t9_172 : Tree 9 := .split 6 t9_173 t9_178
private theorem t9_172OK : treeOK shape9_15 3 4 t9_172=true := by
  change (treeOK shape9_15 3 (4 ||| 2^6) t9_173 && treeOK shape9_15 (3 ||| 2^6) 4 t9_178)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_173OK,t9_178OK⟩

private def t9_179 : Tree 9 := (.tip (.cover 1 3 4 5))
private theorem t9_179OK : treeOK shape9_15 7 0 t9_179=true := by decide

private def t9_171 : Tree 9 := .split 2 t9_172 t9_179
private theorem t9_171OK : treeOK shape9_15 3 0 t9_171=true := by
  change (treeOK shape9_15 3 (0 ||| 2^2) t9_172 && treeOK shape9_15 (3 ||| 2^2) 0 t9_179)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_172OK,t9_179OK⟩

private def t9_153 : Tree 9 := .split 1 t9_154 t9_171
private theorem t9_153OK : treeOK shape9_15 1 0 t9_153=true := by
  change (treeOK shape9_15 1 (0 ||| 2^1) t9_154 && treeOK shape9_15 (1 ||| 2^1) 0 t9_171)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_154OK,t9_171OK⟩

private def t9_131 : Tree 9 := .split 0 t9_132 t9_153
private theorem t9_131OK : treeOK shape9_15 0 0 t9_131=true := by
  change (treeOK shape9_15 0 (0 ||| 2^0) t9_132 && treeOK shape9_15 (0 ||| 2^0) 0 t9_153)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_132OK,t9_153OK⟩

private def shape9_16 : Shape := ⟨true,6,4,2⟩
private def t9_181 : Tree 9 := (.tip (.small 1))
private theorem t9_181OK : treeOK shape9_16 0 1 t9_181=true := by decide

private def t9_185 : Tree 9 := (.split 9 (.tip (.small 1)) (.split 12 (.tip (.cover 1 2 4 6)) (.split 20 (.split 6 (.split 11 (.tip (.cover 1 3 4 5)) (.tip (.cover 0 1 3 4))) (.tip (.cover 0 2 4 7))) (.tip (.cover 1 2 4 7)))))
private theorem t9_185OK : treeOK shape9_16 1 138 t9_185=true := by decide

private def t9_186 : Tree 9 := (.split 4 (.tip (.small 1)) (.split 8 (.split 15 (.tip (.cover 1 3 5 6)) (.tip (.cover 0 3 6 7))) (.split 9 (.tip (.small 1)) (.tip (.cover 0 1 6 7)))))
private theorem t9_186OK : treeOK shape9_16 9 130 t9_186=true := by decide

private def t9_184 : Tree 9 := .split 3 t9_185 t9_186
private theorem t9_184OK : treeOK shape9_16 1 130 t9_184=true := by
  change (treeOK shape9_16 1 (130 ||| 2^3) t9_185 && treeOK shape9_16 (1 ||| 2^3) 130 t9_186)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_185OK,t9_186OK⟩

private def t9_187 : Tree 9 := (.split 8 (.split 2 (.split 9 (.tip (.small 1)) (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 2 5 7)))) (.split 4 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.cover 0 1 5 7))))) (.tip (.cover 1 2 5 6)))
private theorem t9_187OK : treeOK shape9_16 129 2 t9_187=true := by decide

private def t9_183 : Tree 9 := .split 7 t9_184 t9_187
private theorem t9_183OK : treeOK shape9_16 1 2 t9_183=true := by
  change (treeOK shape9_16 1 (2 ||| 2^7) t9_184 && treeOK shape9_16 (1 ||| 2^7) 2 t9_187)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_184OK,t9_187OK⟩

private def t9_188 : Tree 9 := (.split 2 (.split 6 (.split 3 (.split 9 (.tip (.small 1)) (.split 15 (.tip (.cover 1 2 5 6)) (.tip (.cover 1 2 3 5)))) (.tip (.cover 1 3 4 6))) (.split 8 (.split 4 (.tip (.small 1)) (.split 9 (.tip (.small 1)) (.tip (.cover 0 1 4 7)))) (.tip (.cover 1 2 4 6)))) (.tip (.cover 1 3 4 5)))
private theorem t9_188OK : treeOK shape9_16 3 0 t9_188=true := by decide

private def t9_182 : Tree 9 := .split 1 t9_183 t9_188
private theorem t9_182OK : treeOK shape9_16 1 0 t9_182=true := by
  change (treeOK shape9_16 1 (0 ||| 2^1) t9_183 && treeOK shape9_16 (1 ||| 2^1) 0 t9_188)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_183OK,t9_188OK⟩

private def t9_180 : Tree 9 := .split 0 t9_181 t9_182
private theorem t9_180OK : treeOK shape9_16 0 0 t9_180=true := by
  change (treeOK shape9_16 0 (0 ||| 2^0) t9_181 && treeOK shape9_16 (0 ||| 2^0) 0 t9_182)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_181OK,t9_182OK⟩

private def shape9_17 : Shape := ⟨true,6,5,2⟩
private def t9_196 : Tree 9 := (.split 6 (.split 7 (.tip (.small 0)) (.split 12 (.tip (.small 0)) (.split 15 (.tip (.small 0)) (.tip (.cover 2 3 4 5))))) (.split 7 (.split 12 (.tip (.small 0)) (.tip (.cover 2 3 4 5))) (.split 9 (.split 10 (.tip (.small 1)) (.tip (.cover 2 4 5 8))) (.tip (.cover 2 4 5 7)))))
private theorem t9_196OK : treeOK shape9_17 0 1050895 t9_196=true := by decide

private def t9_197 : Tree 9 := (.split 6 (.split 7 (.split 12 (.tip (.small 0)) (.split 15 (.tip (.small 0)) (.tip (.cover 2 3 4 5)))) (.tip (.cover 1 2 3 4))) (.tip (.cover 1 2 3 6)))
private theorem t9_197OK : treeOK shape9_17 4 1050891 t9_197=true := by decide

private def t9_195 : Tree 9 := .split 2 t9_196 t9_197
private theorem t9_195OK : treeOK shape9_17 0 1050891 t9_195=true := by
  change (treeOK shape9_17 0 (1050891 ||| 2^2) t9_196 && treeOK shape9_17 (0 ||| 2^2) 1050891 t9_197)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_196OK,t9_197OK⟩

private def t9_198 : Tree 9 := (.split 2 (.split 6 (.split 7 (.split 12 (.tip (.small 0)) (.tip (.cover 2 3 4 5))) (.tip (.cover 1 2 3 6))) (.tip (.cover 1 2 3 6))) (.split 4 (.split 5 (.tip (.small 1)) (.tip (.cover 3 4 5 8))) (.tip (.cover 3 4 5 7))))
private theorem t9_198OK : treeOK shape9_17 2 1050889 t9_198=true := by decide

private def t9_194 : Tree 9 := .split 1 t9_195 t9_198
private theorem t9_194OK : treeOK shape9_17 0 1050889 t9_194=true := by
  change (treeOK shape9_17 0 (1050889 ||| 2^1) t9_195 && treeOK shape9_17 (0 ||| 2^1) 1050889 t9_198)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_195OK,t9_198OK⟩

private def t9_200 : Tree 9 := (.split 7 (.tip (.cover 1 3 4 5)) (.split 15 (.split 1 (.split 2 (.split 9 (.split 10 (.tip (.small 1)) (.tip (.cover 2 5 6 8))) (.tip (.cover 2 5 6 7))) (.tip (.cover 1 2 3 4))) (.tip (.cover 1 2 5 6))) (.tip (.cover 1 3 4 5))))
private theorem t9_200OK : treeOK shape9_17 256 1050697 t9_200=true := by decide

private def t9_201 : Tree 9 := (.split 7 (.split 12 (.split 1 (.split 2 (.split 9 (.split 10 (.tip (.small 1)) (.tip (.cover 2 4 6 8))) (.tip (.cover 2 4 6 7))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 3 4 5))) (.tip (.cover 1 3 4 5))) (.tip (.cover 1 4 5 6)))
private theorem t9_201OK : treeOK shape9_17 320 1050633 t9_201=true := by decide

private def t9_199 : Tree 9 := .split 6 t9_200 t9_201
private theorem t9_199OK : treeOK shape9_17 256 1050633 t9_199=true := by
  change (treeOK shape9_17 256 (1050633 ||| 2^6) t9_200 && treeOK shape9_17 (256 ||| 2^6) 1050633 t9_201)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_200OK,t9_201OK⟩

private def t9_193 : Tree 9 := .split 8 t9_194 t9_199
private theorem t9_193OK : treeOK shape9_17 0 1050633 t9_193=true := by
  change (treeOK shape9_17 0 (1050633 ||| 2^8) t9_194 && treeOK shape9_17 (0 ||| 2^8) 1050633 t9_199)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_194OK,t9_199OK⟩

private def t9_204 : Tree 9 := (.split 2 (.tip (.cover 1 2 4 5)) (.split 15 (.split 4 (.split 5 (.tip (.small 1)) (.tip (.cover 3 5 6 8))) (.tip (.cover 3 5 6 7))) (.tip (.cover 1 2 4 5))))
private theorem t9_204OK : treeOK shape9_17 8 1050883 t9_204=true := by decide

private def t9_205 : Tree 9 := (.split 2 (.split 12 (.split 4 (.split 5 (.tip (.small 1)) (.tip (.cover 3 4 6 8))) (.tip (.cover 3 4 6 7))) (.tip (.cover 1 2 4 5))) (.tip (.cover 1 4 5 6)))
private theorem t9_205OK : treeOK shape9_17 10 1050881 t9_205=true := by decide

private def t9_203 : Tree 9 := .split 1 t9_204 t9_205
private theorem t9_203OK : treeOK shape9_17 8 1050881 t9_203=true := by
  change (treeOK shape9_17 8 (1050881 ||| 2^1) t9_204 && treeOK shape9_17 (8 ||| 2^1) 1050881 t9_205)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_204OK,t9_205OK⟩

private def t9_206 : Tree 9 := (.split 12 (.split 15 (.tip (.cover 1 4 5 6)) (.tip (.cover 1 2 3 5))) (.tip (.cover 1 2 3 4)))
private theorem t9_206OK : treeOK shape9_17 264 1050625 t9_206=true := by decide

private def t9_202 : Tree 9 := .split 8 t9_203 t9_206
private theorem t9_202OK : treeOK shape9_17 8 1050625 t9_202=true := by
  change (treeOK shape9_17 8 (1050625 ||| 2^8) t9_203 && treeOK shape9_17 (8 ||| 2^8) 1050625 t9_206)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_203OK,t9_206OK⟩

private def t9_192 : Tree 9 := .split 3 t9_193 t9_202
private theorem t9_192OK : treeOK shape9_17 0 1050625 t9_192=true := by
  change (treeOK shape9_17 0 (1050625 ||| 2^3) t9_193 && treeOK shape9_17 (0 ||| 2^3) 1050625 t9_202)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_193OK,t9_202OK⟩

private def t9_210 : Tree 9 := (.split 9 (.split 14 (.split 17 (.split 18 (.tip (.cover 2 3 6 7)) (.tip (.cover 2 3 6 8))) (.tip (.cover 2 3 5 7))) (.tip (.cover 2 3 4 7))) (.split 10 (.split 5 (.tip (.small 1)) (.tip (.cover 1 2 3 6))) (.split 14 (.split 17 (.tip (.cover 1 4 5 8)) (.tip (.cover 2 3 5 7))) (.tip (.cover 2 3 4 7)))))
private theorem t9_210OK : treeOK shape9_17 1048576 2329 t9_210=true := by decide

private def t9_211 : Tree 9 := (.split 5 (.split 9 (.split 10 (.tip (.small 1)) (.tip (.cover 1 2 3 6))) (.tip (.cover 0 2 3 8))) (.split 9 (.split 14 (.split 17 (.tip (.cover 1 4 5 8)) (.tip (.cover 2 3 5 7))) (.tip (.cover 2 3 4 7))) (.tip (.cover 0 2 3 8))))
private theorem t9_211OK : treeOK shape9_17 1048592 2313 t9_211=true := by decide

private def t9_209 : Tree 9 := .split 4 t9_210 t9_211
private theorem t9_209OK : treeOK shape9_17 1048576 2313 t9_209=true := by
  change (treeOK shape9_17 1048576 (2313 ||| 2^4) t9_210 && treeOK shape9_17 (1048576 ||| 2^4) 2313 t9_211)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_210OK,t9_211OK⟩

private def t9_213 : Tree 9 := (.split 4 (.split 10 (.tip (.small 1)) (.split 12 (.split 15 (.tip (.cover 1 4 5 6)) (.tip (.cover 0 1 6 8))) (.tip (.cover 0 1 6 8)))) (.tip (.cover 0 2 3 8)))
private theorem t9_213OK : treeOK shape9_17 1048832 2569 t9_213=true := by decide

private def t9_214 : Tree 9 := (.split 10 (.split 4 (.split 12 (.split 15 (.tip (.cover 1 4 5 6)) (.tip (.cover 0 1 6 7))) (.tip (.cover 0 1 6 7))) (.tip (.cover 0 2 3 8))) (.tip (.cover 2 6 7 8)))
private theorem t9_214OK : treeOK shape9_17 1049344 2057 t9_214=true := by decide

private def t9_212 : Tree 9 := .split 9 t9_213 t9_214
private theorem t9_212OK : treeOK shape9_17 1048832 2057 t9_212=true := by
  change (treeOK shape9_17 1048832 (2057 ||| 2^9) t9_213 && treeOK shape9_17 (1048832 ||| 2^9) 2057 t9_214)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_213OK,t9_214OK⟩

private def t9_208 : Tree 9 := .split 8 t9_209 t9_212
private theorem t9_208OK : treeOK shape9_17 1048576 2057 t9_208=true := by
  change (treeOK shape9_17 1048576 (2057 ||| 2^8) t9_209 && treeOK shape9_17 (1048576 ||| 2^8) 2057 t9_212)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_209OK,t9_212OK⟩

private def t9_216 : Tree 9 := (.split 8 (.split 5 (.split 9 (.tip (.small 1)) (.tip (.cover 0 2 3 8))) (.split 9 (.split 12 (.split 15 (.tip (.cover 1 4 5 6)) (.tip (.cover 0 1 6 8))) (.tip (.cover 0 1 6 8))) (.tip (.cover 0 1 2 7)))) (.tip (.cover 0 2 3 7)))
private theorem t9_216OK : treeOK shape9_17 1048584 2065 t9_216=true := by decide

private def t9_217 : Tree 9 := (.split 5 (.split 8 (.split 9 (.split 12 (.split 15 (.tip (.cover 1 4 5 6)) (.tip (.cover 0 1 6 7))) (.tip (.cover 0 1 6 7))) (.tip (.cover 0 2 3 8))) (.tip (.cover 0 1 6 7))) (.tip (.cover 3 6 7 8)))
private theorem t9_217OK : treeOK shape9_17 1048600 2049 t9_217=true := by decide

private def t9_215 : Tree 9 := .split 4 t9_216 t9_217
private theorem t9_215OK : treeOK shape9_17 1048584 2049 t9_215=true := by
  change (treeOK shape9_17 1048584 (2049 ||| 2^4) t9_216 && treeOK shape9_17 (1048584 ||| 2^4) 2049 t9_217)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_216OK,t9_217OK⟩

private def t9_207 : Tree 9 := .split 3 t9_208 t9_215
private theorem t9_207OK : treeOK shape9_17 1048576 2049 t9_207=true := by
  change (treeOK shape9_17 1048576 (2049 ||| 2^3) t9_208 && treeOK shape9_17 (1048576 ||| 2^3) 2049 t9_215)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_208OK,t9_215OK⟩

private def t9_191 : Tree 9 := .split 20 t9_192 t9_207
private theorem t9_191OK : treeOK shape9_17 0 2049 t9_191=true := by
  change (treeOK shape9_17 0 (2049 ||| 2^20) t9_192 && treeOK shape9_17 (0 ||| 2^20) 2049 t9_207)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_192OK,t9_207OK⟩

private def t9_224 : Tree 9 := (.split 6 (.split 8 (.tip (.small 0)) (.split 15 (.tip (.small 0)) (.tip (.cover 2 3 4 6)))) (.split 8 (.tip (.cover 2 3 4 6)) (.split 9 (.split 10 (.tip (.small 1)) (.tip (.cover 2 4 6 8))) (.tip (.cover 2 4 6 7)))))
private theorem t9_224OK : treeOK shape9_17 2048 1052815 t9_224=true := by decide

private def t9_225 : Tree 9 := (.split 6 (.split 8 (.split 15 (.tip (.small 0)) (.tip (.cover 2 3 4 6))) (.tip (.cover 1 2 3 4))) (.tip (.cover 1 2 3 5)))
private theorem t9_225OK : treeOK shape9_17 2056 1052807 t9_225=true := by decide

private def t9_223 : Tree 9 := .split 3 t9_224 t9_225
private theorem t9_223OK : treeOK shape9_17 2048 1052807 t9_223=true := by
  change (treeOK shape9_17 2048 (1052807 ||| 2^3) t9_224 && treeOK shape9_17 (2048 ||| 2^3) 1052807 t9_225)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_224OK,t9_225OK⟩

private def t9_226 : Tree 9 := (.split 3 (.split 6 (.split 8 (.tip (.cover 2 3 4 6)) (.tip (.cover 1 2 3 5))) (.tip (.cover 1 2 3 5))) (.split 4 (.split 5 (.tip (.small 1)) (.tip (.cover 3 4 6 8))) (.tip (.cover 3 4 6 7))))
private theorem t9_226OK : treeOK shape9_17 2050 1052805 t9_226=true := by decide

private def t9_222 : Tree 9 := .split 1 t9_223 t9_226
private theorem t9_222OK : treeOK shape9_17 2048 1052805 t9_222=true := by
  change (treeOK shape9_17 2048 (1052805 ||| 2^1) t9_223 && treeOK shape9_17 (2048 ||| 2^1) 1052805 t9_226)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_223OK,t9_226OK⟩

private def t9_227 : Tree 9 := (.split 6 (.split 8 (.tip (.cover 1 3 4 6)) (.split 15 (.split 1 (.split 3 (.split 9 (.split 10 (.tip (.small 1)) (.tip (.cover 2 4 6 8))) (.tip (.cover 2 4 6 7))) (.tip (.cover 0 1 5 6))) (.tip (.cover 0 1 3 4))) (.tip (.cover 1 3 4 6)))) (.split 8 (.tip (.cover 1 3 4 6)) (.tip (.cover 1 4 5 6))))
private theorem t9_227OK : treeOK shape9_17 2176 1052677 t9_227=true := by decide

private def t9_221 : Tree 9 := .split 7 t9_222 t9_227
private theorem t9_221OK : treeOK shape9_17 2048 1052677 t9_221=true := by
  change (treeOK shape9_17 2048 (1052677 ||| 2^7) t9_222 && treeOK shape9_17 (2048 ||| 2^7) 1052677 t9_227)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_222OK,t9_227OK⟩

private def t9_228 : Tree 9 := (.split 7 (.split 1 (.split 3 (.tip (.cover 1 2 4 6)) (.split 15 (.split 4 (.split 5 (.tip (.small 1)) (.tip (.cover 3 4 6 8))) (.tip (.cover 3 4 6 7))) (.tip (.cover 1 2 4 6)))) (.split 3 (.tip (.cover 1 2 4 6)) (.tip (.cover 1 4 5 6)))) (.tip (.cover 1 2 3 4)))
private theorem t9_228OK : treeOK shape9_17 2052 1052673 t9_228=true := by decide

private def t9_220 : Tree 9 := .split 2 t9_221 t9_228
private theorem t9_220OK : treeOK shape9_17 2048 1052673 t9_220=true := by
  change (treeOK shape9_17 2048 (1052673 ||| 2^2) t9_221 && treeOK shape9_17 (2048 ||| 2^2) 1052673 t9_228)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_221OK,t9_228OK⟩

private def t9_229 : Tree 9 := (.tip (.cover 2 3 4 7))
private theorem t9_229OK : treeOK shape9_17 1050624 4097 t9_229=true := by decide

private def t9_219 : Tree 9 := .split 20 t9_220 t9_229
private theorem t9_219OK : treeOK shape9_17 2048 4097 t9_219=true := by
  change (treeOK shape9_17 2048 (4097 ||| 2^20) t9_220 && treeOK shape9_17 (2048 ||| 2^20) 4097 t9_229)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_220OK,t9_229OK⟩

private def t9_230 : Tree 9 := (.tip (.cover 2 3 5 6))
private theorem t9_230OK : treeOK shape9_17 6144 1 t9_230=true := by decide

private def t9_218 : Tree 9 := .split 12 t9_219 t9_230
private theorem t9_218OK : treeOK shape9_17 2048 1 t9_218=true := by
  change (treeOK shape9_17 2048 (1 ||| 2^12) t9_219 && treeOK shape9_17 (2048 ||| 2^12) 1 t9_230)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_219OK,t9_230OK⟩

private def t9_190 : Tree 9 := .split 11 t9_191 t9_218
private theorem t9_190OK : treeOK shape9_17 0 1 t9_190=true := by
  change (treeOK shape9_17 0 (1 ||| 2^11) t9_191 && treeOK shape9_17 (0 ||| 2^11) 1 t9_218)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_191OK,t9_218OK⟩

private def t9_235 : Tree 9 := (.split 12 (.tip (.cover 1 2 4 6)) (.split 6 (.split 11 (.tip (.cover 1 3 4 5)) (.tip (.cover 1 2 5 6))) (.split 8 (.split 11 (.tip (.cover 1 3 4 5)) (.tip (.cover 1 2 5 6))) (.tip (.cover 1 2 4 6)))))
private theorem t9_235OK : treeOK shape9_17 1 1048714 t9_235=true := by decide

private def t9_236 : Tree 9 := (.split 8 (.split 15 (.tip (.cover 1 3 5 6)) (.split 2 (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 1 2 5))) (.tip (.cover 1 3 5 6)))) (.split 12 (.tip (.cover 1 2 4 6)) (.tip (.cover 1 2 3 4))))
private theorem t9_236OK : treeOK shape9_17 9 1048706 t9_236=true := by decide

private def t9_234 : Tree 9 := .split 3 t9_235 t9_236
private theorem t9_234OK : treeOK shape9_17 1 1048706 t9_234=true := by
  change (treeOK shape9_17 1 (1048706 ||| 2^3) t9_235 && treeOK shape9_17 (1 ||| 2^3) 1048706 t9_236)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_235OK,t9_236OK⟩

private def t9_237 : Tree 9 := (.split 3 (.split 9 (.split 12 (.tip (.cover 1 2 4 6)) (.tip (.cover 2 3 4 7))) (.split 10 (.split 12 (.tip (.cover 1 2 4 6)) (.tip (.cover 1 2 4 7))) (.tip (.cover 0 2 7 8)))) (.split 4 (.split 8 (.split 15 (.tip (.cover 1 3 5 6)) (.tip (.cover 0 3 6 7))) (.tip (.cover 0 2 3 7))) (.tip (.cover 1 3 6 7))))
private theorem t9_237OK : treeOK shape9_17 1048577 130 t9_237=true := by decide

private def t9_233 : Tree 9 := .split 20 t9_234 t9_237
private theorem t9_233OK : treeOK shape9_17 1 130 t9_233=true := by
  change (treeOK shape9_17 1 (130 ||| 2^20) t9_234 && treeOK shape9_17 (1 ||| 2^20) 130 t9_237)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_234OK,t9_237OK⟩

private def t9_240 : Tree 9 := (.split 2 (.split 11 (.tip (.cover 1 2 4 5)) (.split 6 (.split 12 (.tip (.cover 1 3 4 6)) (.tip (.cover 0 1 3 4))) (.tip (.cover 1 2 4 5)))) (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 2 3 4))))
private theorem t9_240OK : treeOK shape9_17 129 1048834 t9_240=true := by decide

private def t9_241 : Tree 9 := (.split 2 (.split 9 (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 0 2 5 7))) (.tip (.cover 1 2 5 7))) (.tip (.cover 0 2 3 7)))
private theorem t9_241OK : treeOK shape9_17 1048705 258 t9_241=true := by decide

private def t9_239 : Tree 9 := .split 20 t9_240 t9_241
private theorem t9_239OK : treeOK shape9_17 129 258 t9_239=true := by
  change (treeOK shape9_17 129 (258 ||| 2^20) t9_240 && treeOK shape9_17 (129 ||| 2^20) 258 t9_241)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_240OK,t9_241OK⟩

private def t9_242 : Tree 9 := (.tip (.cover 1 2 5 6))
private theorem t9_242OK : treeOK shape9_17 385 2 t9_242=true := by decide

private def t9_238 : Tree 9 := .split 8 t9_239 t9_242
private theorem t9_238OK : treeOK shape9_17 129 2 t9_238=true := by
  change (treeOK shape9_17 129 (2 ||| 2^8) t9_239 && treeOK shape9_17 (129 ||| 2^8) 2 t9_242)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_239OK,t9_242OK⟩

private def t9_232 : Tree 9 := .split 7 t9_233 t9_238
private theorem t9_232OK : treeOK shape9_17 1 2 t9_232=true := by
  change (treeOK shape9_17 1 (2 ||| 2^7) t9_233 && treeOK shape9_17 (1 ||| 2^7) 2 t9_238)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_233OK,t9_238OK⟩

private def t9_245 : Tree 9 := (.split 20 (.split 3 (.split 15 (.tip (.cover 1 2 5 6)) (.tip (.cover 1 3 4 5))) (.tip (.cover 1 3 4 6))) (.split 3 (.split 9 (.split 15 (.tip (.cover 1 2 5 6)) (.tip (.cover 1 3 4 5))) (.tip (.cover 0 1 2 7))) (.tip (.cover 1 3 4 6))))
private theorem t9_245OK : treeOK shape9_17 3 68 t9_245=true := by decide

private def t9_246 : Tree 9 := (.split 8 (.split 20 (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 2 3 5))) (.tip (.cover 0 2 3 7))) (.tip (.cover 1 2 4 6)))
private theorem t9_246OK : treeOK shape9_17 67 4 t9_246=true := by decide

private def t9_244 : Tree 9 := .split 6 t9_245 t9_246
private theorem t9_244OK : treeOK shape9_17 3 4 t9_244=true := by
  change (treeOK shape9_17 3 (4 ||| 2^6) t9_245 && treeOK shape9_17 (3 ||| 2^6) 4 t9_246)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_245OK,t9_246OK⟩

private def t9_247 : Tree 9 := (.tip (.cover 1 3 4 5))
private theorem t9_247OK : treeOK shape9_17 7 0 t9_247=true := by decide

private def t9_243 : Tree 9 := .split 2 t9_244 t9_247
private theorem t9_243OK : treeOK shape9_17 3 0 t9_243=true := by
  change (treeOK shape9_17 3 (0 ||| 2^2) t9_244 && treeOK shape9_17 (3 ||| 2^2) 0 t9_247)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_244OK,t9_247OK⟩

private def t9_231 : Tree 9 := .split 1 t9_232 t9_243
private theorem t9_231OK : treeOK shape9_17 1 0 t9_231=true := by
  change (treeOK shape9_17 1 (0 ||| 2^1) t9_232 && treeOK shape9_17 (1 ||| 2^1) 0 t9_243)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_232OK,t9_243OK⟩

private def t9_189 : Tree 9 := .split 0 t9_190 t9_231
private theorem t9_189OK : treeOK shape9_17 0 0 t9_189=true := by
  change (treeOK shape9_17 0 (0 ||| 2^0) t9_190 && treeOK shape9_17 (0 ||| 2^0) 0 t9_231)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_190OK,t9_231OK⟩

private def shape9_18 : Shape := ⟨true,7,4,2⟩
private def t9_249 : Tree 9 := (.tip (.small 1))
private theorem t9_249OK : treeOK shape9_18 0 1 t9_249=true := by decide

private def t9_253 : Tree 9 := (.split 5 (.tip (.small 1)) (.split 10 (.tip (.small 1)) (.split 2 (.tip (.cover 1 2 3 5)) (.split 3 (.split 4 (.tip (.cover 1 2 6 7)) (.tip (.cover 1 3 5 7))) (.tip (.cover 1 3 5 6))))))
private theorem t9_253OK : treeOK shape9_18 1 262274 t9_253=true := by decide

private def t9_254 : Tree 9 := (.split 3 (.split 9 (.split 12 (.tip (.cover 1 2 4 6)) (.tip (.cover 1 2 4 7))) (.split 10 (.tip (.small 1)) (.tip (.cover 0 2 7 8)))) (.split 4 (.split 8 (.split 13 (.tip (.cover 1 2 4 7)) (.tip (.cover 0 1 2 7))) (.tip (.cover 1 2 3 7))) (.tip (.cover 1 3 6 7))))
private theorem t9_254OK : treeOK shape9_18 262145 130 t9_254=true := by decide

private def t9_252 : Tree 9 := .split 18 t9_253 t9_254
private theorem t9_252OK : treeOK shape9_18 1 130 t9_252=true := by
  change (treeOK shape9_18 1 (130 ||| 2^18) t9_253 && treeOK shape9_18 (1 ||| 2^18) 130 t9_254)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_253OK,t9_254OK⟩

private def t9_256 : Tree 9 := (.split 16 (.split 5 (.tip (.small 1)) (.split 10 (.tip (.small 1)) (.split 2 (.split 4 (.tip (.cover 1 2 5 7)) (.tip (.cover 1 5 7 8))) (.tip (.cover 0 1 5 8))))) (.split 2 (.split 9 (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 2 4 7))) (.tip (.cover 1 2 5 7))) (.tip (.cover 1 2 3 7))))
private theorem t9_256OK : treeOK shape9_18 129 258 t9_256=true := by decide

private def t9_257 : Tree 9 := (.tip (.cover 1 2 5 6))
private theorem t9_257OK : treeOK shape9_18 385 2 t9_257=true := by decide

private def t9_255 : Tree 9 := .split 8 t9_256 t9_257
private theorem t9_255OK : treeOK shape9_18 129 2 t9_255=true := by
  change (treeOK shape9_18 129 (2 ||| 2^8) t9_256 && treeOK shape9_18 (129 ||| 2^8) 2 t9_257)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_256OK,t9_257OK⟩

private def t9_251 : Tree 9 := .split 7 t9_252 t9_255
private theorem t9_251OK : treeOK shape9_18 1 2 t9_251=true := by
  change (treeOK shape9_18 1 (2 ||| 2^7) t9_252 && treeOK shape9_18 (1 ||| 2^7) 2 t9_255)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_252OK,t9_255OK⟩

private def t9_260 : Tree 9 := (.split 18 (.split 5 (.tip (.small 1)) (.split 10 (.tip (.small 1)) (.split 3 (.split 4 (.tip (.cover 1 2 6 7)) (.tip (.cover 1 3 4 7))) (.tip (.cover 1 3 4 6))))) (.tip (.cover 1 3 4 6)))
private theorem t9_260OK : treeOK shape9_18 3 68 t9_260=true := by decide

private def t9_261 : Tree 9 := (.split 8 (.split 13 (.split 5 (.tip (.small 1)) (.split 10 (.tip (.small 1)) (.tip (.cover 0 1 4 8)))) (.tip (.cover 1 2 3 7))) (.tip (.cover 1 2 4 6)))
private theorem t9_261OK : treeOK shape9_18 67 4 t9_261=true := by decide

private def t9_259 : Tree 9 := .split 6 t9_260 t9_261
private theorem t9_259OK : treeOK shape9_18 3 4 t9_259=true := by
  change (treeOK shape9_18 3 (4 ||| 2^6) t9_260 && treeOK shape9_18 (3 ||| 2^6) 4 t9_261)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_260OK,t9_261OK⟩

private def t9_262 : Tree 9 := (.tip (.cover 1 3 4 5))
private theorem t9_262OK : treeOK shape9_18 7 0 t9_262=true := by decide

private def t9_258 : Tree 9 := .split 2 t9_259 t9_262
private theorem t9_258OK : treeOK shape9_18 3 0 t9_258=true := by
  change (treeOK shape9_18 3 (0 ||| 2^2) t9_259 && treeOK shape9_18 (3 ||| 2^2) 0 t9_262)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_259OK,t9_262OK⟩

private def t9_250 : Tree 9 := .split 1 t9_251 t9_258
private theorem t9_250OK : treeOK shape9_18 1 0 t9_250=true := by
  change (treeOK shape9_18 1 (0 ||| 2^1) t9_251 && treeOK shape9_18 (1 ||| 2^1) 0 t9_258)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_251OK,t9_258OK⟩

private def t9_248 : Tree 9 := .split 0 t9_249 t9_250
private theorem t9_248OK : treeOK shape9_18 0 0 t9_248=true := by
  change (treeOK shape9_18 0 (0 ||| 2^0) t9_249 && treeOK shape9_18 (0 ||| 2^0) 0 t9_250)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_249OK,t9_250OK⟩

private def shape9_19 : Shape := ⟨true,4,4,3⟩
private def t9_264 : Tree 9 := (.split 1 (.tip (.small 0)) (.split 6 (.tip (.small 0)) (.split 11 (.tip (.cover 0 1 4 5)) (.split 12 (.tip (.cover 0 1 4 6)) (.split 13 (.tip (.cover 0 1 4 7)) (.split 14 (.tip (.cover 0 1 4 8)) (.split 15 (.tip (.cover 0 1 5 6)) (.tip (.cover 0 2 3 5)))))))))
private theorem t9_264OK : treeOK shape9_19 0 1 t9_264=true := by decide

private def t9_266 : Tree 9 := (.split 6 (.tip (.small 0)) (.split 7 (.tip (.cover 0 1 3 5)) (.split 8 (.tip (.cover 0 1 3 6)) (.split 9 (.tip (.cover 0 1 3 7)) (.split 10 (.tip (.cover 0 1 3 8)) (.split 15 (.tip (.cover 0 1 5 6)) (.tip (.cover 0 2 4 5))))))))
private theorem t9_266OK : treeOK shape9_19 1 2 t9_266=true := by decide

private def t9_268 : Tree 9 := (.split 2 (.tip (.cover 0 1 2 5)) (.split 3 (.tip (.cover 0 1 2 6)) (.split 4 (.tip (.cover 0 1 2 7)) (.split 5 (.tip (.cover 0 1 2 8)) (.split 15 (.tip (.cover 0 1 5 6)) (.tip (.cover 0 3 4 5)))))))
private theorem t9_268OK : treeOK shape9_19 3 64 t9_268=true := by decide

private def t9_269 : Tree 9 := (.split 2 (.tip (.cover 0 1 2 5)) (.split 3 (.tip (.cover 0 1 2 6)) (.split 4 (.tip (.cover 0 1 2 7)) (.split 5 (.tip (.cover 0 1 2 8)) (.split 7 (.tip (.cover 0 1 3 5)) (.tip (.cover 0 1 4 5)))))))
private theorem t9_269OK : treeOK shape9_19 67 0 t9_269=true := by decide

private def t9_267 : Tree 9 := .split 6 t9_268 t9_269
private theorem t9_267OK : treeOK shape9_19 3 0 t9_267=true := by
  change (treeOK shape9_19 3 (0 ||| 2^6) t9_268 && treeOK shape9_19 (3 ||| 2^6) 0 t9_269)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_268OK,t9_269OK⟩

private def t9_265 : Tree 9 := .split 1 t9_266 t9_267
private theorem t9_265OK : treeOK shape9_19 1 0 t9_265=true := by
  change (treeOK shape9_19 1 (0 ||| 2^1) t9_266 && treeOK shape9_19 (1 ||| 2^1) 0 t9_267)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_266OK,t9_267OK⟩

private def t9_263 : Tree 9 := .split 0 t9_264 t9_265
private theorem t9_263OK : treeOK shape9_19 0 0 t9_263=true := by
  change (treeOK shape9_19 0 (0 ||| 2^0) t9_264 && treeOK shape9_19 (0 ||| 2^0) 0 t9_265)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_264OK,t9_265OK⟩

private def shape9_20 : Shape := ⟨true,5,4,3⟩
private def t9_271 : Tree 9 := (.split 1 (.tip (.small 1)) (.split 6 (.tip (.small 1)) (.split 11 (.split 18 (.tip (.cover 0 1 6 7)) (.split 19 (.tip (.cover 0 1 6 8)) (.tip (.cover 0 1 4 6)))) (.tip (.cover 1 2 3 5)))))
private theorem t9_271OK : treeOK shape9_20 0 1 t9_271=true := by decide

private def t9_273 : Tree 9 := (.split 6 (.tip (.small 1)) (.split 7 (.split 18 (.tip (.cover 0 1 6 7)) (.split 19 (.tip (.cover 0 1 6 8)) (.tip (.cover 0 1 3 6)))) (.tip (.cover 1 2 4 5))))
private theorem t9_273OK : treeOK shape9_20 1 2 t9_273=true := by decide

private def t9_274 : Tree 9 := (.split 6 (.split 2 (.split 18 (.tip (.cover 0 1 6 7)) (.split 19 (.tip (.cover 0 1 6 8)) (.tip (.cover 0 1 2 6)))) (.tip (.cover 1 3 4 5))) (.split 2 (.split 7 (.tip (.cover 1 2 3 5)) (.tip (.cover 1 2 4 5))) (.tip (.cover 1 3 4 5))))
private theorem t9_274OK : treeOK shape9_20 3 0 t9_274=true := by decide

private def t9_272 : Tree 9 := .split 1 t9_273 t9_274
private theorem t9_272OK : treeOK shape9_20 1 0 t9_272=true := by
  change (treeOK shape9_20 1 (0 ||| 2^1) t9_273 && treeOK shape9_20 (1 ||| 2^1) 0 t9_274)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_273OK,t9_274OK⟩

private def t9_270 : Tree 9 := .split 0 t9_271 t9_272
private theorem t9_270OK : treeOK shape9_20 0 0 t9_270=true := by
  change (treeOK shape9_20 0 (0 ||| 2^0) t9_271 && treeOK shape9_20 (0 ||| 2^0) 0 t9_272)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_271OK,t9_272OK⟩

private def shape9_21 : Shape := ⟨true,5,5,3⟩
private def t9_280 : Tree 9 := (.tip (.cover 0 1 7 8))
private theorem t9_280OK : treeOK shape9_21 0 1081411 t9_280=true := by decide

private def t9_285 : Tree 9 := (.split 14 (.tip (.rank 3)) (.split 11 (.split 12 (.tip (.rank 0)) (.tip (.cover 2 3 6 8))) (.tip (.cover 2 3 5 8))))
private theorem t9_285OK : treeOK shape9_21 1048576 361571 t9_285=true := by decide

private def t9_286 : Tree 9 := (.split 14 (.split 7 (.split 8 (.tip (.rank 0)) (.tip (.cover 2 4 6 8))) (.tip (.cover 2 4 5 8))) (.split 7 (.split 8 (.split 11 (.tip (.small 0)) (.tip (.cover 2 3 5 8))) (.tip (.cover 2 4 6 8))) (.tip (.cover 2 4 5 8))))
private theorem t9_286OK : treeOK shape9_21 1049600 360547 t9_286=true := by decide

private def t9_284 : Tree 9 := .split 10 t9_285 t9_286
private theorem t9_284OK : treeOK shape9_21 1048576 360547 t9_284=true := by
  change (treeOK shape9_21 1048576 (360547 ||| 2^10) t9_285 && treeOK shape9_21 (1048576 ||| 2^10) 360547 t9_286)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_285OK,t9_286OK⟩

private def t9_288 : Tree 9 := (.split 14 (.split 2 (.split 3 (.tip (.rank 0)) (.tip (.cover 3 4 6 8))) (.tip (.cover 3 4 5 8))) (.split 2 (.split 3 (.split 11 (.tip (.small 0)) (.tip (.cover 2 3 5 8))) (.tip (.cover 3 4 6 8))) (.tip (.cover 3 4 5 8))))
private theorem t9_288OK : treeOK shape9_21 1048608 361539 t9_288=true := by decide

private def t9_289 : Tree 9 := (.split 14 (.split 2 (.split 3 (.split 7 (.tip (.small 0)) (.tip (.cover 2 4 5 8))) (.tip (.cover 3 4 6 8))) (.tip (.cover 3 4 5 8))) (.tip (.cover 0 2 3 4)))
private theorem t9_289OK : treeOK shape9_21 1049632 360515 t9_289=true := by decide

private def t9_287 : Tree 9 := .split 10 t9_288 t9_289
private theorem t9_287OK : treeOK shape9_21 1048608 360515 t9_287=true := by
  change (treeOK shape9_21 1048608 (360515 ||| 2^10) t9_288 && treeOK shape9_21 (1048608 ||| 2^10) 360515 t9_289)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_288OK,t9_289OK⟩

private def t9_283 : Tree 9 := .split 5 t9_284 t9_287
private theorem t9_283OK : treeOK shape9_21 1048576 360515 t9_283=true := by
  change (treeOK shape9_21 1048576 (360515 ||| 2^5) t9_284 && treeOK shape9_21 (1048576 ||| 2^5) 360515 t9_287)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_284OK,t9_287OK⟩

private def t9_290 : Tree 9 := (.tip (.cover 2 3 4 6))
private theorem t9_290OK : treeOK shape9_21 1310720 98371 t9_290=true := by decide

private def t9_282 : Tree 9 := .split 18 t9_283 t9_290
private theorem t9_282OK : treeOK shape9_21 1048576 98371 t9_282=true := by
  change (treeOK shape9_21 1048576 (98371 ||| 2^18) t9_283 && treeOK shape9_21 (1048576 ||| 2^18) 98371 t9_290)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_283OK,t9_290OK⟩

private def t9_291 : Tree 9 := (.tip (.cover 2 3 4 5))
private theorem t9_291OK : treeOK shape9_21 1114112 32835 t9_291=true := by decide

private def t9_281 : Tree 9 := .split 16 t9_282 t9_291
private theorem t9_281OK : treeOK shape9_21 1048576 32835 t9_281=true := by
  change (treeOK shape9_21 1048576 (32835 ||| 2^16) t9_282 && treeOK shape9_21 (1048576 ||| 2^16) 32835 t9_291)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_282OK,t9_291OK⟩

private def t9_279 : Tree 9 := .split 20 t9_280 t9_281
private theorem t9_279OK : treeOK shape9_21 0 32835 t9_279=true := by
  change (treeOK shape9_21 0 (32835 ||| 2^20) t9_280 && treeOK shape9_21 (0 ||| 2^20) 32835 t9_281)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_280OK,t9_281OK⟩

private def t9_292 : Tree 9 := (.tip (.cover 2 3 4 5))
private theorem t9_292OK : treeOK shape9_21 32768 67 t9_292=true := by decide

private def t9_278 : Tree 9 := .split 15 t9_279 t9_292
private theorem t9_278OK : treeOK shape9_21 0 67 t9_278=true := by
  change (treeOK shape9_21 0 (67 ||| 2^15) t9_279 && treeOK shape9_21 (0 ||| 2^15) 67 t9_292)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_279OK,t9_292OK⟩

private def t9_295 : Tree 9 := (.split 20 (.tip (.cover 0 1 7 8)) (.split 2 (.split 18 (.split 10 (.split 11 (.tip (.small 0)) (.split 13 (.tip (.cover 0 1 4 7)) (.tip (.cover 1 3 5 7)))) (.split 11 (.tip (.small 0)) (.tip (.cover 0 1 4 8)))) (.tip (.cover 2 3 4 6))) (.split 3 (.tip (.cover 0 2 4 6)) (.tip (.cover 3 4 5 6)))))
private theorem t9_295OK : treeOK shape9_21 64 4227 t9_295=true := by decide

private def t9_296 : Tree 9 := (.split 18 (.split 2 (.split 11 (.tip (.small 0)) (.tip (.cover 2 3 5 6))) (.tip (.cover 0 2 3 6))) (.tip (.cover 2 3 4 6)))
private theorem t9_296OK : treeOK shape9_21 4160 131 t9_296=true := by decide

private def t9_294 : Tree 9 := .split 12 t9_295 t9_296
private theorem t9_294OK : treeOK shape9_21 64 131 t9_294=true := by
  change (treeOK shape9_21 64 (131 ||| 2^12) t9_295 && treeOK shape9_21 (64 ||| 2^12) 131 t9_296)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_295OK,t9_296OK⟩

private def t9_297 : Tree 9 := (.split 8 (.split 11 (.split 20 (.tip (.cover 0 1 7 8)) (.split 2 (.split 18 (.split 9 (.tip (.cover 0 1 3 7)) (.tip (.cover 1 4 5 7))) (.tip (.cover 0 1 3 7))) (.split 3 (.tip (.cover 0 2 3 6)) (.tip (.cover 0 1 2 3))))) (.split 16 (.tip (.cover 0 1 5 7)) (.tip (.cover 2 3 4 5)))) (.tip (.cover 2 4 5 6)))
private theorem t9_297OK : treeOK shape9_21 192 3 t9_297=true := by decide

private def t9_293 : Tree 9 := .split 7 t9_294 t9_297
private theorem t9_293OK : treeOK shape9_21 64 3 t9_293=true := by
  change (treeOK shape9_21 64 (3 ||| 2^7) t9_294 && treeOK shape9_21 (64 ||| 2^7) 3 t9_297)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_294OK,t9_297OK⟩

private def t9_277 : Tree 9 := .split 6 t9_278 t9_293
private theorem t9_277OK : treeOK shape9_21 0 3 t9_277=true := by
  change (treeOK shape9_21 0 (3 ||| 2^6) t9_278 && treeOK shape9_21 (0 ||| 2^6) 3 t9_293)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_278OK,t9_293OK⟩

private def t9_301 : Tree 9 := (.split 20 (.tip (.cover 0 1 7 8)) (.split 7 (.split 18 (.split 5 (.split 11 (.tip (.small 0)) (.split 13 (.tip (.cover 0 1 4 7)) (.tip (.cover 1 2 5 7)))) (.split 11 (.tip (.small 0)) (.tip (.cover 0 1 4 8)))) (.tip (.cover 2 3 4 6))) (.split 8 (.tip (.cover 0 3 4 6)) (.tip (.cover 2 4 5 6)))))
private theorem t9_301OK : treeOK shape9_21 2 4165 t9_301=true := by decide

private def t9_302 : Tree 9 := (.split 18 (.split 7 (.split 11 (.tip (.small 0)) (.tip (.cover 2 3 5 6))) (.tip (.cover 0 2 3 6))) (.tip (.cover 2 3 4 6)))
private theorem t9_302OK : treeOK shape9_21 4098 69 t9_302=true := by decide

private def t9_300 : Tree 9 := .split 12 t9_301 t9_302
private theorem t9_300OK : treeOK shape9_21 2 69 t9_300=true := by
  change (treeOK shape9_21 2 (69 ||| 2^12) t9_301 && treeOK shape9_21 (2 ||| 2^12) 69 t9_302)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_301OK,t9_302OK⟩

private def t9_303 : Tree 9 := (.split 3 (.split 11 (.split 20 (.tip (.cover 0 1 7 8)) (.split 7 (.split 18 (.split 4 (.tip (.cover 0 1 2 7)) (.tip (.cover 1 4 5 7))) (.tip (.cover 0 1 2 7))) (.split 8 (.tip (.cover 0 2 3 6)) (.tip (.cover 0 1 2 3))))) (.split 16 (.tip (.cover 0 1 5 7)) (.tip (.cover 2 3 4 5)))) (.tip (.cover 3 4 5 6)))
private theorem t9_303OK : treeOK shape9_21 6 65 t9_303=true := by decide

private def t9_299 : Tree 9 := .split 2 t9_300 t9_303
private theorem t9_299OK : treeOK shape9_21 2 65 t9_299=true := by
  change (treeOK shape9_21 2 (65 ||| 2^2) t9_300 && treeOK shape9_21 (2 ||| 2^2) 65 t9_303)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_300OK,t9_303OK⟩

private def t9_304 : Tree 9 := (.split 11 (.split 3 (.split 8 (.tip (.cover 0 2 3 6)) (.split 20 (.tip (.cover 0 1 7 8)) (.split 7 (.tip (.cover 1 3 4 5)) (.tip (.cover 2 4 5 6))))) (.split 8 (.split 20 (.tip (.cover 0 1 7 8)) (.split 2 (.tip (.cover 1 2 4 5)) (.tip (.cover 3 4 5 6)))) (.tip (.cover 0 1 2 3)))) (.tip (.cover 1 2 3 5)))
private theorem t9_304OK : treeOK shape9_21 66 1 t9_304=true := by decide

private def t9_298 : Tree 9 := .split 6 t9_299 t9_304
private theorem t9_298OK : treeOK shape9_21 2 1 t9_298=true := by
  change (treeOK shape9_21 2 (1 ||| 2^6) t9_299 && treeOK shape9_21 (2 ||| 2^6) 1 t9_304)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_299OK,t9_304OK⟩

private def t9_276 : Tree 9 := .split 1 t9_277 t9_298
private theorem t9_276OK : treeOK shape9_21 0 1 t9_276=true := by
  change (treeOK shape9_21 0 (1 ||| 2^1) t9_277 && treeOK shape9_21 (0 ||| 2^1) 1 t9_298)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_277OK,t9_298OK⟩

private def t9_309 : Tree 9 := (.split 20 (.tip (.cover 0 1 7 8)) (.split 11 (.split 18 (.split 5 (.split 7 (.tip (.small 0)) (.split 9 (.tip (.cover 0 1 3 7)) (.tip (.cover 1 2 5 7)))) (.split 7 (.tip (.small 0)) (.tip (.cover 0 1 3 8)))) (.tip (.cover 2 3 4 6))) (.split 12 (.tip (.cover 0 3 4 6)) (.tip (.cover 2 3 5 6)))))
private theorem t9_309OK : treeOK shape9_21 1 326 t9_309=true := by decide

private def t9_310 : Tree 9 := (.split 18 (.split 7 (.split 11 (.tip (.small 0)) (.tip (.cover 0 2 4 6))) (.tip (.cover 2 4 5 6))) (.tip (.cover 2 3 4 6)))
private theorem t9_310OK : treeOK shape9_21 257 70 t9_310=true := by decide

private def t9_308 : Tree 9 := .split 8 t9_309 t9_310
private theorem t9_308OK : treeOK shape9_21 1 70 t9_308=true := by
  change (treeOK shape9_21 1 (70 ||| 2^8) t9_309 && treeOK shape9_21 (1 ||| 2^8) 70 t9_310)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_309OK,t9_310OK⟩

private def t9_311 : Tree 9 := (.split 3 (.split 7 (.split 20 (.tip (.cover 0 1 7 8)) (.split 11 (.split 18 (.split 4 (.tip (.cover 0 1 2 7)) (.tip (.cover 1 3 5 7))) (.tip (.cover 0 1 2 7))) (.split 12 (.tip (.cover 0 2 4 6)) (.tip (.cover 0 1 2 4))))) (.split 16 (.tip (.cover 0 1 5 7)) (.tip (.cover 2 3 4 5)))) (.tip (.cover 3 4 5 6)))
private theorem t9_311OK : treeOK shape9_21 5 66 t9_311=true := by decide

private def t9_307 : Tree 9 := .split 2 t9_308 t9_311
private theorem t9_307OK : treeOK shape9_21 1 66 t9_307=true := by
  change (treeOK shape9_21 1 (66 ||| 2^2) t9_308 && treeOK shape9_21 (1 ||| 2^2) 66 t9_311)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_308OK,t9_311OK⟩

private def t9_313 : Tree 9 := (.split 3 (.split 12 (.tip (.cover 0 2 4 6)) (.split 20 (.tip (.cover 0 1 7 8)) (.split 8 (.split 11 (.tip (.cover 1 3 4 5)) (.tip (.cover 2 3 5 6))) (.tip (.cover 0 2 4 6))))) (.split 8 (.split 20 (.tip (.cover 0 1 7 8)) (.split 2 (.tip (.cover 1 2 3 5)) (.tip (.cover 3 4 5 6)))) (.tip (.cover 0 2 4 6))))
private theorem t9_313OK : treeOK shape9_21 65 130 t9_313=true := by decide

private def t9_314 : Tree 9 := (.tip (.cover 1 2 4 5))
private theorem t9_314OK : treeOK shape9_21 193 2 t9_314=true := by decide

private def t9_312 : Tree 9 := .split 7 t9_313 t9_314
private theorem t9_312OK : treeOK shape9_21 65 2 t9_312=true := by
  change (treeOK shape9_21 65 (2 ||| 2^7) t9_313 && treeOK shape9_21 (65 ||| 2^7) 2 t9_314)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_313OK,t9_314OK⟩

private def t9_306 : Tree 9 := .split 6 t9_307 t9_312
private theorem t9_306OK : treeOK shape9_21 1 2 t9_306=true := by
  change (treeOK shape9_21 1 (2 ||| 2^6) t9_307 && treeOK shape9_21 (1 ||| 2^6) 2 t9_312)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_307OK,t9_312OK⟩

private def t9_316 : Tree 9 := (.split 2 (.split 3 (.split 20 (.tip (.cover 0 1 7 8)) (.split 7 (.split 11 (.tip (.cover 1 3 4 5)) (.split 12 (.tip (.cover 0 2 4 6)) (.tip (.cover 2 3 5 6)))) (.split 8 (.tip (.cover 0 2 3 6)) (.tip (.cover 2 4 5 6))))) (.tip (.cover 0 3 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t9_316OK : treeOK shape9_21 3 64 t9_316=true := by decide

private def t9_317 : Tree 9 := (.split 2 (.split 8 (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 2 3 5))) (.tip (.cover 0 2 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t9_317OK : treeOK shape9_21 67 0 t9_317=true := by decide

private def t9_315 : Tree 9 := .split 6 t9_316 t9_317
private theorem t9_315OK : treeOK shape9_21 3 0 t9_315=true := by
  change (treeOK shape9_21 3 (0 ||| 2^6) t9_316 && treeOK shape9_21 (3 ||| 2^6) 0 t9_317)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_316OK,t9_317OK⟩

private def t9_305 : Tree 9 := .split 1 t9_306 t9_315
private theorem t9_305OK : treeOK shape9_21 1 0 t9_305=true := by
  change (treeOK shape9_21 1 (0 ||| 2^1) t9_306 && treeOK shape9_21 (1 ||| 2^1) 0 t9_315)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_306OK,t9_315OK⟩

private def t9_275 : Tree 9 := .split 0 t9_276 t9_305
private theorem t9_275OK : treeOK shape9_21 0 0 t9_275=true := by
  change (treeOK shape9_21 0 (0 ||| 2^0) t9_276 && treeOK shape9_21 (0 ||| 2^0) 0 t9_305)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_276OK,t9_305OK⟩

private def shape9_22 : Shape := ⟨true,6,4,3⟩
private def t9_320 : Tree 9 := (.tip (.small 1))
private theorem t9_320OK : treeOK shape9_22 0 3 t9_320=true := by decide

private def t9_322 : Tree 9 := (.tip (.small 1))
private theorem t9_322OK : treeOK shape9_22 2 65 t9_322=true := by decide

private def t9_323 : Tree 9 := (.split 11 (.split 3 (.split 8 (.tip (.cover 1 2 3 6)) (.split 20 (.tip (.cover 0 1 7 8)) (.split 7 (.tip (.cover 1 3 4 5)) (.tip (.cover 1 2 5 6))))) (.split 8 (.split 20 (.tip (.cover 0 1 7 8)) (.split 2 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 3 5 6)))) (.tip (.cover 0 1 4 6)))) (.tip (.cover 1 2 3 5)))
private theorem t9_323OK : treeOK shape9_22 66 1 t9_323=true := by decide

private def t9_321 : Tree 9 := .split 6 t9_322 t9_323
private theorem t9_321OK : treeOK shape9_22 2 1 t9_321=true := by
  change (treeOK shape9_22 2 (1 ||| 2^6) t9_322 && treeOK shape9_22 (2 ||| 2^6) 1 t9_323)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_322OK,t9_323OK⟩

private def t9_319 : Tree 9 := .split 1 t9_320 t9_321
private theorem t9_319OK : treeOK shape9_22 0 1 t9_319=true := by
  change (treeOK shape9_22 0 (1 ||| 2^1) t9_320 && treeOK shape9_22 (0 ||| 2^1) 1 t9_321)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_320OK,t9_321OK⟩

private def t9_326 : Tree 9 := (.tip (.small 1))
private theorem t9_326OK : treeOK shape9_22 1 66 t9_326=true := by decide

private def t9_327 : Tree 9 := (.split 7 (.split 3 (.split 12 (.tip (.cover 1 2 4 6)) (.split 20 (.tip (.cover 0 1 7 8)) (.split 8 (.split 11 (.tip (.cover 1 3 4 5)) (.tip (.cover 1 2 5 6))) (.tip (.cover 1 2 4 6))))) (.split 8 (.split 15 (.tip (.cover 1 3 5 6)) (.tip (.cover 0 1 3 6))) (.tip (.cover 1 2 4 6)))) (.tip (.cover 1 2 4 5)))
private theorem t9_327OK : treeOK shape9_22 65 2 t9_327=true := by decide

private def t9_325 : Tree 9 := .split 6 t9_326 t9_327
private theorem t9_325OK : treeOK shape9_22 1 2 t9_325=true := by
  change (treeOK shape9_22 1 (2 ||| 2^6) t9_326 && treeOK shape9_22 (1 ||| 2^6) 2 t9_327)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_326OK,t9_327OK⟩

private def t9_328 : Tree 9 := (.split 6 (.split 2 (.split 3 (.split 15 (.tip (.cover 1 2 5 6)) (.tip (.cover 1 3 4 5))) (.tip (.cover 1 3 4 6))) (.tip (.cover 1 3 4 5))) (.split 2 (.split 8 (.split 11 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 2 3 5))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 3 4 5))))
private theorem t9_328OK : treeOK shape9_22 3 0 t9_328=true := by decide

private def t9_324 : Tree 9 := .split 1 t9_325 t9_328
private theorem t9_324OK : treeOK shape9_22 1 0 t9_324=true := by
  change (treeOK shape9_22 1 (0 ||| 2^1) t9_325 && treeOK shape9_22 (1 ||| 2^1) 0 t9_328)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_325OK,t9_328OK⟩

private def t9_318 : Tree 9 := .split 0 t9_319 t9_324
private theorem t9_318OK : treeOK shape9_22 0 0 t9_318=true := by
  change (treeOK shape9_22 0 (0 ||| 2^0) t9_319 && treeOK shape9_22 (0 ||| 2^0) 0 t9_324)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_319OK,t9_324OK⟩

private def shape9_23 : Shape := ⟨true,6,5,3⟩
private def t9_337 : Tree 9 := (.split 8 (.tip (.cover 2 3 5 6)) (.split 11 (.tip (.cover 2 3 4 5)) (.split 12 (.split 9 (.tip (.rank 0)) (.tip (.cover 2 4 6 7))) (.tip (.cover 2 3 5 6)))))
private theorem t9_337OK : treeOK shape9_23 0 1081551 t9_337=true := by decide

private def t9_338 : Tree 9 := (.split 8 (.split 11 (.split 12 (.tip (.small 0)) (.split 9 (.tip (.rank 0)) (.tip (.cover 2 4 5 7)))) (.tip (.cover 2 3 5 6))) (.tip (.cover 2 4 5 6)))
private theorem t9_338OK : treeOK shape9_23 128 1081423 t9_338=true := by decide

private def t9_336 : Tree 9 := .split 7 t9_337 t9_338
private theorem t9_336OK : treeOK shape9_23 0 1081423 t9_336=true := by
  change (treeOK shape9_23 0 (1081423 ||| 2^7) t9_337 && treeOK shape9_23 (0 ||| 2^7) 1081423 t9_338)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_337OK,t9_338OK⟩

private def t9_340 : Tree 9 := (.split 8 (.split 11 (.tip (.cover 2 3 4 5)) (.split 12 (.split 4 (.tip (.rank 0)) (.tip (.cover 3 4 6 7))) (.tip (.cover 2 3 5 6)))) (.tip (.cover 1 2 3 5)))
private theorem t9_340OK : treeOK shape9_23 8 1081543 t9_340=true := by decide

private def t9_341 : Tree 9 := (.split 8 (.split 11 (.split 12 (.split 4 (.tip (.rank 0)) (.tip (.cover 3 4 6 7))) (.tip (.cover 0 2 3 4))) (.tip (.cover 0 2 3 4))) (.tip (.cover 2 4 5 6)))
private theorem t9_341OK : treeOK shape9_23 136 1081415 t9_341=true := by decide

private def t9_339 : Tree 9 := .split 7 t9_340 t9_341
private theorem t9_339OK : treeOK shape9_23 8 1081415 t9_339=true := by
  change (treeOK shape9_23 8 (1081415 ||| 2^7) t9_340 && treeOK shape9_23 (8 ||| 2^7) 1081415 t9_341)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_340OK,t9_341OK⟩

private def t9_335 : Tree 9 := .split 3 t9_336 t9_339
private theorem t9_335OK : treeOK shape9_23 0 1081415 t9_335=true := by
  change (treeOK shape9_23 0 (1081415 ||| 2^3) t9_336 && treeOK shape9_23 (0 ||| 2^3) 1081415 t9_339)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_336OK,t9_339OK⟩

private def t9_344 : Tree 9 := (.split 8 (.split 11 (.split 12 (.tip (.small 0)) (.split 4 (.tip (.rank 0)) (.tip (.cover 3 4 5 7)))) (.tip (.cover 2 3 5 6))) (.split 11 (.split 12 (.split 4 (.tip (.rank 0)) (.tip (.cover 3 4 5 7))) (.tip (.cover 0 2 3 4))) (.tip (.cover 0 2 3 4))))
private theorem t9_344OK : treeOK shape9_23 4 1081547 t9_344=true := by decide

private def t9_345 : Tree 9 := (.split 8 (.tip (.cover 1 2 3 6)) (.tip (.cover 2 4 5 6)))
private theorem t9_345OK : treeOK shape9_23 132 1081419 t9_345=true := by decide

private def t9_343 : Tree 9 := .split 7 t9_344 t9_345
private theorem t9_343OK : treeOK shape9_23 4 1081419 t9_343=true := by
  change (treeOK shape9_23 4 (1081419 ||| 2^7) t9_344 && treeOK shape9_23 (4 ||| 2^7) 1081419 t9_345)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_344OK,t9_345OK⟩

private def t9_346 : Tree 9 := (.tip (.cover 3 4 5 6))
private theorem t9_346OK : treeOK shape9_23 12 1081411 t9_346=true := by decide

private def t9_342 : Tree 9 := .split 3 t9_343 t9_346
private theorem t9_342OK : treeOK shape9_23 4 1081411 t9_342=true := by
  change (treeOK shape9_23 4 (1081411 ||| 2^3) t9_343 && treeOK shape9_23 (4 ||| 2^3) 1081411 t9_346)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_343OK,t9_346OK⟩

private def t9_334 : Tree 9 := .split 2 t9_335 t9_342
private theorem t9_334OK : treeOK shape9_23 0 1081411 t9_334=true := by
  change (treeOK shape9_23 0 (1081411 ||| 2^2) t9_335 && treeOK shape9_23 (0 ||| 2^2) 1081411 t9_342)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_335OK,t9_342OK⟩

private def t9_347 : Tree 9 := (.tip (.cover 2 3 4 7))
private theorem t9_347OK : treeOK shape9_23 1048576 32835 t9_347=true := by decide

private def t9_333 : Tree 9 := .split 20 t9_334 t9_347
private theorem t9_333OK : treeOK shape9_23 0 32835 t9_333=true := by
  change (treeOK shape9_23 0 (32835 ||| 2^20) t9_334 && treeOK shape9_23 (0 ||| 2^20) 32835 t9_347)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_334OK,t9_347OK⟩

private def t9_348 : Tree 9 := (.tip (.cover 2 3 4 5))
private theorem t9_348OK : treeOK shape9_23 32768 67 t9_348=true := by decide

private def t9_332 : Tree 9 := .split 15 t9_333 t9_348
private theorem t9_332OK : treeOK shape9_23 0 67 t9_332=true := by
  change (treeOK shape9_23 0 (67 ||| 2^15) t9_333 && treeOK shape9_23 (0 ||| 2^15) 67 t9_348)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_333OK,t9_348OK⟩

private def t9_352 : Tree 9 := (.split 11 (.split 12 (.tip (.cover 1 4 5 6)) (.split 19 (.split 13 (.tip (.small 1)) (.tip (.cover 2 3 6 7))) (.tip (.cover 1 4 5 6)))) (.split 12 (.split 17 (.split 13 (.tip (.small 1)) (.tip (.cover 2 3 5 7))) (.tip (.cover 1 4 5 6))) (.tip (.cover 1 3 5 6))))
private theorem t9_352OK : treeOK shape9_23 64 33299 t9_352=true := by decide

private def t9_353 : Tree 9 := (.split 11 (.split 12 (.tip (.cover 1 4 5 6)) (.tip (.cover 1 2 3 6))) (.tip (.cover 1 2 3 5)))
private theorem t9_353OK : treeOK shape9_23 80 33283 t9_353=true := by decide

private def t9_351 : Tree 9 := .split 4 t9_352 t9_353
private theorem t9_351OK : treeOK shape9_23 64 33283 t9_351=true := by
  change (treeOK shape9_23 64 (33283 ||| 2^4) t9_352 && treeOK shape9_23 (64 ||| 2^4) 33283 t9_353)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_352OK,t9_353OK⟩

private def t9_354 : Tree 9 := (.split 13 (.split 4 (.split 7 (.split 8 (.tip (.cover 1 3 5 6)) (.tip (.cover 2 4 6 7))) (.tip (.cover 2 4 5 7))) (.split 7 (.split 8 (.tip (.cover 1 3 5 6)) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 2 4 5)))) (.split 20 (.tip (.cover 0 1 7 8)) (.tip (.cover 2 3 4 7))))
private theorem t9_354OK : treeOK shape9_23 576 32771 t9_354=true := by decide

private def t9_350 : Tree 9 := .split 9 t9_351 t9_354
private theorem t9_350OK : treeOK shape9_23 64 32771 t9_350=true := by
  change (treeOK shape9_23 64 (32771 ||| 2^9) t9_351 && treeOK shape9_23 (64 ||| 2^9) 32771 t9_354)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_351OK,t9_354OK⟩

private def t9_355 : Tree 9 := (.tip (.cover 2 3 4 5))
private theorem t9_355OK : treeOK shape9_23 32832 3 t9_355=true := by decide

private def t9_349 : Tree 9 := .split 15 t9_350 t9_355
private theorem t9_349OK : treeOK shape9_23 64 3 t9_349=true := by
  change (treeOK shape9_23 64 (3 ||| 2^15) t9_350 && treeOK shape9_23 (64 ||| 2^15) 3 t9_355)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_350OK,t9_355OK⟩

private def t9_331 : Tree 9 := .split 6 t9_332 t9_349
private theorem t9_331OK : treeOK shape9_23 0 3 t9_331=true := by
  change (treeOK shape9_23 0 (3 ||| 2^6) t9_332 && treeOK shape9_23 (0 ||| 2^6) 3 t9_349)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_332OK,t9_349OK⟩

private def t9_360 : Tree 9 := (.split 11 (.split 12 (.tip (.cover 1 4 5 6)) (.split 19 (.split 13 (.tip (.small 1)) (.tip (.cover 2 3 6 7))) (.tip (.cover 1 4 5 6)))) (.split 12 (.split 17 (.split 13 (.tip (.small 1)) (.tip (.cover 2 3 5 7))) (.tip (.cover 1 4 5 6))) (.tip (.cover 1 2 5 6))))
private theorem t9_360OK : treeOK shape9_23 2 33361 t9_360=true := by decide

private def t9_361 : Tree 9 := (.split 11 (.split 12 (.tip (.cover 1 4 5 6)) (.tip (.cover 1 2 3 6))) (.tip (.cover 1 2 3 5)))
private theorem t9_361OK : treeOK shape9_23 514 32849 t9_361=true := by decide

private def t9_359 : Tree 9 := .split 9 t9_360 t9_361
private theorem t9_359OK : treeOK shape9_23 2 32849 t9_359=true := by
  change (treeOK shape9_23 2 (32849 ||| 2^9) t9_360 && treeOK shape9_23 (2 ||| 2^9) 32849 t9_361)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_360OK,t9_361OK⟩

private def t9_362 : Tree 9 := (.split 13 (.split 2 (.split 3 (.tip (.cover 1 2 5 6)) (.tip (.cover 3 4 6 7))) (.tip (.cover 3 4 5 7))) (.split 20 (.tip (.cover 0 1 7 8)) (.tip (.cover 2 3 4 7))))
private theorem t9_362OK : treeOK shape9_23 18 32833 t9_362=true := by decide

private def t9_358 : Tree 9 := .split 4 t9_359 t9_362
private theorem t9_358OK : treeOK shape9_23 2 32833 t9_358=true := by
  change (treeOK shape9_23 2 (32833 ||| 2^4) t9_359 && treeOK shape9_23 (2 ||| 2^4) 32833 t9_362)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_359OK,t9_362OK⟩

private def t9_363 : Tree 9 := (.tip (.cover 2 3 4 5))
private theorem t9_363OK : treeOK shape9_23 32770 65 t9_363=true := by decide

private def t9_357 : Tree 9 := .split 15 t9_358 t9_363
private theorem t9_357OK : treeOK shape9_23 2 65 t9_357=true := by
  change (treeOK shape9_23 2 (65 ||| 2^15) t9_358 && treeOK shape9_23 (2 ||| 2^15) 65 t9_363)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_358OK,t9_363OK⟩

private def t9_364 : Tree 9 := (.split 11 (.split 3 (.split 8 (.tip (.cover 1 2 3 6)) (.split 9 (.split 4 (.tip (.cover 0 2 3 7)) (.tip (.cover 0 1 2 3))) (.tip (.cover 2 4 6 7)))) (.split 4 (.split 8 (.split 9 (.tip (.cover 0 2 3 7)) (.tip (.cover 0 1 2 3))) (.tip (.cover 0 1 2 3))) (.tip (.cover 3 4 6 7)))) (.tip (.cover 1 2 3 5)))
private theorem t9_364OK : treeOK shape9_23 66 1 t9_364=true := by decide

private def t9_356 : Tree 9 := .split 6 t9_357 t9_364
private theorem t9_356OK : treeOK shape9_23 2 1 t9_356=true := by
  change (treeOK shape9_23 2 (1 ||| 2^6) t9_357 && treeOK shape9_23 (2 ||| 2^6) 1 t9_364)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_357OK,t9_364OK⟩

private def t9_330 : Tree 9 := .split 1 t9_331 t9_356
private theorem t9_330OK : treeOK shape9_23 0 1 t9_330=true := by
  change (treeOK shape9_23 0 (1 ||| 2^1) t9_331 && treeOK shape9_23 (0 ||| 2^1) 1 t9_356)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_331OK,t9_356OK⟩

private def t9_370 : Tree 9 := (.split 8 (.tip (.cover 1 3 5 6)) (.split 13 (.split 19 (.split 9 (.tip (.small 1)) (.tip (.cover 2 4 6 7))) (.tip (.cover 1 3 5 6))) (.tip (.cover 1 2 4 6))))
private theorem t9_370OK : treeOK shape9_23 1 32978 t9_370=true := by decide

private def t9_371 : Tree 9 := (.split 8 (.split 13 (.split 17 (.split 9 (.tip (.small 1)) (.tip (.cover 2 4 5 7))) (.tip (.cover 1 3 5 6))) (.tip (.cover 1 2 4 5))) (.tip (.cover 1 2 5 6)))
private theorem t9_371OK : treeOK shape9_23 129 32850 t9_371=true := by decide

private def t9_369 : Tree 9 := .split 7 t9_370 t9_371
private theorem t9_369OK : treeOK shape9_23 1 32850 t9_369=true := by
  change (treeOK shape9_23 1 (32850 ||| 2^7) t9_370 && treeOK shape9_23 (1 ||| 2^7) 32850 t9_371)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_370OK,t9_371OK⟩

private def t9_372 : Tree 9 := (.split 9 (.split 2 (.split 3 (.tip (.cover 1 2 5 6)) (.tip (.cover 3 4 6 7))) (.tip (.cover 3 4 5 7))) (.split 20 (.tip (.cover 0 1 7 8)) (.tip (.cover 2 3 4 7))))
private theorem t9_372OK : treeOK shape9_23 17 32834 t9_372=true := by decide

private def t9_368 : Tree 9 := .split 4 t9_369 t9_372
private theorem t9_368OK : treeOK shape9_23 1 32834 t9_368=true := by
  change (treeOK shape9_23 1 (32834 ||| 2^4) t9_369 && treeOK shape9_23 (1 ||| 2^4) 32834 t9_372)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_369OK,t9_372OK⟩

private def t9_373 : Tree 9 := (.tip (.cover 2 3 4 5))
private theorem t9_373OK : treeOK shape9_23 32769 66 t9_373=true := by decide

private def t9_367 : Tree 9 := .split 15 t9_368 t9_373
private theorem t9_367OK : treeOK shape9_23 1 66 t9_367=true := by
  change (treeOK shape9_23 1 (66 ||| 2^15) t9_368 && treeOK shape9_23 (1 ||| 2^15) 66 t9_373)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_368OK,t9_373OK⟩

private def t9_374 : Tree 9 := (.split 7 (.split 3 (.split 9 (.split 12 (.tip (.cover 1 2 4 6)) (.split 11 (.tip (.cover 1 3 4 5)) (.tip (.cover 1 2 5 6)))) (.tip (.cover 0 2 4 7))) (.split 4 (.split 8 (.split 13 (.tip (.cover 0 2 4 7)) (.tip (.cover 0 1 2 4))) (.tip (.cover 1 2 4 6))) (.tip (.cover 3 4 6 7)))) (.tip (.cover 1 2 4 5)))
private theorem t9_374OK : treeOK shape9_23 65 2 t9_374=true := by decide

private def t9_366 : Tree 9 := .split 6 t9_367 t9_374
private theorem t9_366OK : treeOK shape9_23 1 2 t9_366=true := by
  change (treeOK shape9_23 1 (2 ||| 2^6) t9_367 && treeOK shape9_23 (1 ||| 2^6) 2 t9_374)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_367OK,t9_374OK⟩

private def t9_376 : Tree 9 := (.split 2 (.split 3 (.split 9 (.split 13 (.tip (.cover 0 3 4 7)) (.split 15 (.tip (.cover 1 2 5 6)) (.tip (.cover 1 2 4 5)))) (.split 13 (.split 15 (.tip (.cover 1 2 5 6)) (.tip (.cover 1 2 3 5))) (.tip (.cover 0 1 2 7)))) (.tip (.cover 1 3 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t9_376OK : treeOK shape9_23 3 64 t9_376=true := by decide

private def t9_377 : Tree 9 := (.split 2 (.split 8 (.split 13 (.split 3 (.tip (.cover 1 2 3 6)) (.tip (.cover 1 3 4 6))) (.tip (.cover 0 2 3 7))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t9_377OK : treeOK shape9_23 67 0 t9_377=true := by decide

private def t9_375 : Tree 9 := .split 6 t9_376 t9_377
private theorem t9_375OK : treeOK shape9_23 3 0 t9_375=true := by
  change (treeOK shape9_23 3 (0 ||| 2^6) t9_376 && treeOK shape9_23 (3 ||| 2^6) 0 t9_377)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_376OK,t9_377OK⟩

private def t9_365 : Tree 9 := .split 1 t9_366 t9_375
private theorem t9_365OK : treeOK shape9_23 1 0 t9_365=true := by
  change (treeOK shape9_23 1 (0 ||| 2^1) t9_366 && treeOK shape9_23 (1 ||| 2^1) 0 t9_375)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_366OK,t9_375OK⟩

private def t9_329 : Tree 9 := .split 0 t9_330 t9_365
private theorem t9_329OK : treeOK shape9_23 0 0 t9_329=true := by
  change (treeOK shape9_23 0 (0 ||| 2^0) t9_330 && treeOK shape9_23 (0 ||| 2^0) 0 t9_365)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_330OK,t9_365OK⟩

private def shape9_24 : Shape := ⟨true,6,6,3⟩
private def t9_386 : Tree 9 := (.split 8 (.tip (.cover 2 3 5 6)) (.split 11 (.tip (.cover 2 3 4 5)) (.split 12 (.split 9 (.split 10 (.tip (.cover 0 3 7 8)) (.tip (.cover 2 4 6 8))) (.tip (.cover 2 4 6 7))) (.tip (.cover 2 3 5 6)))))
private theorem t9_386OK : treeOK shape9_24 0 1081551 t9_386=true := by decide

private def t9_387 : Tree 9 := (.split 8 (.split 11 (.split 12 (.tip (.small 0)) (.split 9 (.split 10 (.tip (.cover 0 3 7 8)) (.tip (.cover 2 4 5 8))) (.tip (.cover 2 4 5 7)))) (.tip (.cover 2 3 5 6))) (.tip (.cover 2 4 5 6)))
private theorem t9_387OK : treeOK shape9_24 128 1081423 t9_387=true := by decide

private def t9_385 : Tree 9 := .split 7 t9_386 t9_387
private theorem t9_385OK : treeOK shape9_24 0 1081423 t9_385=true := by
  change (treeOK shape9_24 0 (1081423 ||| 2^7) t9_386 && treeOK shape9_24 (0 ||| 2^7) 1081423 t9_387)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_386OK,t9_387OK⟩

private def t9_389 : Tree 9 := (.split 8 (.split 11 (.tip (.cover 2 3 4 5)) (.split 12 (.split 4 (.split 5 (.tip (.cover 0 2 7 8)) (.tip (.cover 3 4 6 8))) (.tip (.cover 3 4 6 7))) (.tip (.cover 2 3 5 6)))) (.tip (.cover 1 2 3 5)))
private theorem t9_389OK : treeOK shape9_24 8 1081543 t9_389=true := by decide

private def t9_390 : Tree 9 := (.split 8 (.split 11 (.split 12 (.split 4 (.split 5 (.tip (.cover 0 2 7 8)) (.tip (.cover 3 4 6 8))) (.tip (.cover 3 4 6 7))) (.tip (.cover 0 2 3 4))) (.tip (.cover 0 2 3 4))) (.tip (.cover 2 4 5 6)))
private theorem t9_390OK : treeOK shape9_24 136 1081415 t9_390=true := by decide

private def t9_388 : Tree 9 := .split 7 t9_389 t9_390
private theorem t9_388OK : treeOK shape9_24 8 1081415 t9_388=true := by
  change (treeOK shape9_24 8 (1081415 ||| 2^7) t9_389 && treeOK shape9_24 (8 ||| 2^7) 1081415 t9_390)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_389OK,t9_390OK⟩

private def t9_384 : Tree 9 := .split 3 t9_385 t9_388
private theorem t9_384OK : treeOK shape9_24 0 1081415 t9_384=true := by
  change (treeOK shape9_24 0 (1081415 ||| 2^3) t9_385 && treeOK shape9_24 (0 ||| 2^3) 1081415 t9_388)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_385OK,t9_388OK⟩

private def t9_394 : Tree 9 := (.split 11 (.split 12 (.tip (.small 0)) (.split 4 (.split 5 (.tip (.cover 0 2 7 8)) (.tip (.cover 3 4 5 8))) (.tip (.cover 3 4 5 7)))) (.tip (.cover 2 3 5 6)))
private theorem t9_394OK : treeOK shape9_24 4 1081803 t9_394=true := by decide

private def t9_395 : Tree 9 := (.split 11 (.split 12 (.split 4 (.split 5 (.tip (.cover 0 2 7 8)) (.tip (.cover 3 4 5 8))) (.tip (.cover 3 4 5 7))) (.tip (.cover 0 2 3 4))) (.tip (.cover 0 2 3 4)))
private theorem t9_395OK : treeOK shape9_24 260 1081547 t9_395=true := by decide

private def t9_393 : Tree 9 := .split 8 t9_394 t9_395
private theorem t9_393OK : treeOK shape9_24 4 1081547 t9_393=true := by
  change (treeOK shape9_24 4 (1081547 ||| 2^8) t9_394 && treeOK shape9_24 (4 ||| 2^8) 1081547 t9_395)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_394OK,t9_395OK⟩

private def t9_396 : Tree 9 := (.split 8 (.tip (.cover 1 2 3 6)) (.tip (.cover 2 4 5 6)))
private theorem t9_396OK : treeOK shape9_24 132 1081419 t9_396=true := by decide

private def t9_392 : Tree 9 := .split 7 t9_393 t9_396
private theorem t9_392OK : treeOK shape9_24 4 1081419 t9_392=true := by
  change (treeOK shape9_24 4 (1081419 ||| 2^7) t9_393 && treeOK shape9_24 (4 ||| 2^7) 1081419 t9_396)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_393OK,t9_396OK⟩

private def t9_397 : Tree 9 := (.tip (.cover 3 4 5 6))
private theorem t9_397OK : treeOK shape9_24 12 1081411 t9_397=true := by decide

private def t9_391 : Tree 9 := .split 3 t9_392 t9_397
private theorem t9_391OK : treeOK shape9_24 4 1081411 t9_391=true := by
  change (treeOK shape9_24 4 (1081411 ||| 2^3) t9_392 && treeOK shape9_24 (4 ||| 2^3) 1081411 t9_397)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_392OK,t9_397OK⟩

private def t9_383 : Tree 9 := .split 2 t9_384 t9_391
private theorem t9_383OK : treeOK shape9_24 0 1081411 t9_383=true := by
  change (treeOK shape9_24 0 (1081411 ||| 2^2) t9_384 && treeOK shape9_24 (0 ||| 2^2) 1081411 t9_391)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_384OK,t9_391OK⟩

private def t9_398 : Tree 9 := (.tip (.cover 2 3 4 7))
private theorem t9_398OK : treeOK shape9_24 1048576 32835 t9_398=true := by decide

private def t9_382 : Tree 9 := .split 20 t9_383 t9_398
private theorem t9_382OK : treeOK shape9_24 0 32835 t9_382=true := by
  change (treeOK shape9_24 0 (32835 ||| 2^20) t9_383 && treeOK shape9_24 (0 ||| 2^20) 32835 t9_398)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_383OK,t9_398OK⟩

private def t9_399 : Tree 9 := (.tip (.cover 2 3 4 5))
private theorem t9_399OK : treeOK shape9_24 32768 67 t9_399=true := by decide

private def t9_381 : Tree 9 := .split 15 t9_382 t9_399
private theorem t9_381OK : treeOK shape9_24 0 67 t9_381=true := by
  change (treeOK shape9_24 0 (67 ||| 2^15) t9_382 && treeOK shape9_24 (0 ||| 2^15) 67 t9_399)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_382OK,t9_399OK⟩

private def t9_403 : Tree 9 := (.split 8 (.tip (.cover 1 3 5 6)) (.split 12 (.split 2 (.split 3 (.split 9 (.split 10 (.tip (.cover 0 3 7 8)) (.tip (.cover 2 4 6 8))) (.tip (.cover 2 4 6 7))) (.tip (.cover 1 2 3 5))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 3 5 6))))
private theorem t9_403OK : treeOK shape9_24 64 1081475 t9_403=true := by decide

private def t9_404 : Tree 9 := (.split 8 (.split 11 (.split 2 (.split 3 (.split 9 (.split 10 (.tip (.cover 0 3 7 8)) (.tip (.cover 2 4 5 8))) (.tip (.cover 2 4 5 7))) (.tip (.cover 1 2 4 5))) (.tip (.cover 1 3 5 6))) (.tip (.cover 1 3 5 6))) (.tip (.cover 1 4 5 6)))
private theorem t9_404OK : treeOK shape9_24 192 1081347 t9_404=true := by decide

private def t9_402 : Tree 9 := .split 7 t9_403 t9_404
private theorem t9_402OK : treeOK shape9_24 64 1081347 t9_402=true := by
  change (treeOK shape9_24 64 (1081347 ||| 2^7) t9_403 && treeOK shape9_24 (64 ||| 2^7) 1081347 t9_404)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_403OK,t9_404OK⟩

private def t9_405 : Tree 9 := (.tip (.cover 2 3 4 7))
private theorem t9_405OK : treeOK shape9_24 1048640 32771 t9_405=true := by decide

private def t9_401 : Tree 9 := .split 20 t9_402 t9_405
private theorem t9_401OK : treeOK shape9_24 64 32771 t9_401=true := by
  change (treeOK shape9_24 64 (32771 ||| 2^20) t9_402 && treeOK shape9_24 (64 ||| 2^20) 32771 t9_405)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_402OK,t9_405OK⟩

private def t9_406 : Tree 9 := (.tip (.cover 2 3 4 5))
private theorem t9_406OK : treeOK shape9_24 32832 3 t9_406=true := by decide

private def t9_400 : Tree 9 := .split 15 t9_401 t9_406
private theorem t9_400OK : treeOK shape9_24 64 3 t9_400=true := by
  change (treeOK shape9_24 64 (3 ||| 2^15) t9_401 && treeOK shape9_24 (64 ||| 2^15) 3 t9_406)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_401OK,t9_406OK⟩

private def t9_380 : Tree 9 := .split 6 t9_381 t9_400
private theorem t9_380OK : treeOK shape9_24 0 3 t9_380=true := by
  change (treeOK shape9_24 0 (3 ||| 2^6) t9_381 && treeOK shape9_24 (0 ||| 2^6) 3 t9_400)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_381OK,t9_400OK⟩

private def t9_411 : Tree 9 := (.split 3 (.tip (.cover 1 2 5 6)) (.split 12 (.split 4 (.split 5 (.tip (.cover 0 2 7 8)) (.tip (.cover 3 4 6 8))) (.tip (.cover 3 4 6 7))) (.tip (.cover 1 2 5 6))))
private theorem t9_411OK : treeOK shape9_24 2 1081413 t9_411=true := by decide

private def t9_412 : Tree 9 := (.split 3 (.split 11 (.split 4 (.split 5 (.tip (.cover 0 2 7 8)) (.tip (.cover 3 4 5 8))) (.tip (.cover 3 4 5 7))) (.tip (.cover 1 2 5 6))) (.tip (.cover 1 4 5 6)))
private theorem t9_412OK : treeOK shape9_24 6 1081409 t9_412=true := by decide

private def t9_410 : Tree 9 := .split 2 t9_411 t9_412
private theorem t9_410OK : treeOK shape9_24 2 1081409 t9_410=true := by
  change (treeOK shape9_24 2 (1081409 ||| 2^2) t9_411 && treeOK shape9_24 (2 ||| 2^2) 1081409 t9_412)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_411OK,t9_412OK⟩

private def t9_413 : Tree 9 := (.tip (.cover 2 3 4 7))
private theorem t9_413OK : treeOK shape9_24 1048578 32833 t9_413=true := by decide

private def t9_409 : Tree 9 := .split 20 t9_410 t9_413
private theorem t9_409OK : treeOK shape9_24 2 32833 t9_409=true := by
  change (treeOK shape9_24 2 (32833 ||| 2^20) t9_410 && treeOK shape9_24 (2 ||| 2^20) 32833 t9_413)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_410OK,t9_413OK⟩

private def t9_414 : Tree 9 := (.tip (.cover 2 3 4 5))
private theorem t9_414OK : treeOK shape9_24 32770 65 t9_414=true := by decide

private def t9_408 : Tree 9 := .split 15 t9_409 t9_414
private theorem t9_408OK : treeOK shape9_24 2 65 t9_408=true := by
  change (treeOK shape9_24 2 (65 ||| 2^15) t9_409 && treeOK shape9_24 (2 ||| 2^15) 65 t9_414)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_409OK,t9_414OK⟩

private def t9_415 : Tree 9 := (.split 11 (.split 20 (.split 3 (.split 8 (.tip (.cover 1 2 3 6)) (.split 7 (.tip (.cover 1 3 4 5)) (.tip (.cover 1 2 5 6)))) (.split 8 (.split 2 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 3 5 6))) (.tip (.cover 0 1 2 3)))) (.tip (.cover 0 2 3 7))) (.tip (.cover 1 2 3 5)))
private theorem t9_415OK : treeOK shape9_24 66 1 t9_415=true := by decide

private def t9_407 : Tree 9 := .split 6 t9_408 t9_415
private theorem t9_407OK : treeOK shape9_24 2 1 t9_407=true := by
  change (treeOK shape9_24 2 (1 ||| 2^6) t9_408 && treeOK shape9_24 (2 ||| 2^6) 1 t9_415)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_408OK,t9_415OK⟩

private def t9_379 : Tree 9 := .split 1 t9_380 t9_407
private theorem t9_379OK : treeOK shape9_24 0 1 t9_379=true := by
  change (treeOK shape9_24 0 (1 ||| 2^1) t9_380 && treeOK shape9_24 (0 ||| 2^1) 1 t9_407)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_380OK,t9_407OK⟩

private def t9_421 : Tree 9 := (.split 3 (.tip (.cover 1 2 5 6)) (.split 8 (.split 4 (.split 5 (.tip (.cover 0 2 7 8)) (.tip (.cover 3 4 6 8))) (.tip (.cover 3 4 6 7))) (.tip (.cover 1 2 5 6))))
private theorem t9_421OK : treeOK shape9_24 1 1081414 t9_421=true := by decide

private def t9_422 : Tree 9 := (.split 3 (.split 7 (.split 4 (.split 5 (.tip (.cover 0 2 7 8)) (.tip (.cover 3 4 5 8))) (.tip (.cover 3 4 5 7))) (.tip (.cover 1 2 5 6))) (.tip (.cover 1 3 5 6)))
private theorem t9_422OK : treeOK shape9_24 5 1081410 t9_422=true := by decide

private def t9_420 : Tree 9 := .split 2 t9_421 t9_422
private theorem t9_420OK : treeOK shape9_24 1 1081410 t9_420=true := by
  change (treeOK shape9_24 1 (1081410 ||| 2^2) t9_421 && treeOK shape9_24 (1 ||| 2^2) 1081410 t9_422)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_421OK,t9_422OK⟩

private def t9_423 : Tree 9 := (.tip (.cover 2 3 4 7))
private theorem t9_423OK : treeOK shape9_24 1048577 32834 t9_423=true := by decide

private def t9_419 : Tree 9 := .split 20 t9_420 t9_423
private theorem t9_419OK : treeOK shape9_24 1 32834 t9_419=true := by
  change (treeOK shape9_24 1 (32834 ||| 2^20) t9_420 && treeOK shape9_24 (1 ||| 2^20) 32834 t9_423)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_420OK,t9_423OK⟩

private def t9_424 : Tree 9 := (.tip (.cover 2 3 4 5))
private theorem t9_424OK : treeOK shape9_24 32769 66 t9_424=true := by decide

private def t9_418 : Tree 9 := .split 15 t9_419 t9_424
private theorem t9_418OK : treeOK shape9_24 1 66 t9_418=true := by
  change (treeOK shape9_24 1 (66 ||| 2^15) t9_419 && treeOK shape9_24 (1 ||| 2^15) 66 t9_424)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_419OK,t9_424OK⟩

private def t9_425 : Tree 9 := (.split 7 (.split 20 (.split 3 (.split 12 (.tip (.cover 1 2 4 6)) (.split 8 (.split 11 (.tip (.cover 1 3 4 5)) (.tip (.cover 1 2 5 6))) (.tip (.cover 1 2 4 6)))) (.split 8 (.split 15 (.tip (.cover 1 3 5 6)) (.tip (.cover 0 1 3 6))) (.tip (.cover 1 2 4 6)))) (.tip (.cover 0 2 4 7))) (.tip (.cover 1 2 4 5)))
private theorem t9_425OK : treeOK shape9_24 65 2 t9_425=true := by decide

private def t9_417 : Tree 9 := .split 6 t9_418 t9_425
private theorem t9_417OK : treeOK shape9_24 1 2 t9_417=true := by
  change (treeOK shape9_24 1 (2 ||| 2^6) t9_418 && treeOK shape9_24 (1 ||| 2^6) 2 t9_425)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_418OK,t9_425OK⟩

private def t9_427 : Tree 9 := (.split 2 (.split 20 (.split 3 (.split 15 (.tip (.cover 1 2 5 6)) (.tip (.cover 1 3 4 5))) (.tip (.cover 1 3 4 6))) (.tip (.cover 0 3 4 7))) (.tip (.cover 1 3 4 5)))
private theorem t9_427OK : treeOK shape9_24 3 64 t9_427=true := by decide

private def t9_428 : Tree 9 := (.split 2 (.split 8 (.split 13 (.split 5 (.split 7 (.tip (.cover 1 2 3 5)) (.tip (.cover 1 2 4 5))) (.tip (.cover 0 3 4 8))) (.tip (.cover 0 2 3 7))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t9_428OK : treeOK shape9_24 67 0 t9_428=true := by decide

private def t9_426 : Tree 9 := .split 6 t9_427 t9_428
private theorem t9_426OK : treeOK shape9_24 3 0 t9_426=true := by
  change (treeOK shape9_24 3 (0 ||| 2^6) t9_427 && treeOK shape9_24 (3 ||| 2^6) 0 t9_428)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_427OK,t9_428OK⟩

private def t9_416 : Tree 9 := .split 1 t9_417 t9_426
private theorem t9_416OK : treeOK shape9_24 1 0 t9_416=true := by
  change (treeOK shape9_24 1 (0 ||| 2^1) t9_417 && treeOK shape9_24 (1 ||| 2^1) 0 t9_426)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_417OK,t9_426OK⟩

private def t9_378 : Tree 9 := .split 0 t9_379 t9_416
private theorem t9_378OK : treeOK shape9_24 0 0 t9_378=true := by
  change (treeOK shape9_24 0 (0 ||| 2^0) t9_379 && treeOK shape9_24 (0 ||| 2^0) 0 t9_416)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_379OK,t9_416OK⟩

private def shape9_25 : Shape := ⟨true,7,4,3⟩
private def t9_431 : Tree 9 := (.tip (.small 1))
private theorem t9_431OK : treeOK shape9_25 0 3 t9_431=true := by decide

private def t9_433 : Tree 9 := (.tip (.small 1))
private theorem t9_433OK : treeOK shape9_25 2 65 t9_433=true := by decide

private def t9_434 : Tree 9 := (.split 11 (.split 18 (.split 2 (.split 7 (.tip (.cover 1 2 3 5)) (.split 8 (.split 9 (.tip (.cover 1 3 6 7)) (.tip (.cover 1 2 5 7))) (.tip (.cover 1 2 5 6)))) (.split 3 (.split 4 (.tip (.cover 1 2 6 7)) (.tip (.cover 1 3 5 7))) (.tip (.cover 1 3 5 6)))) (.tip (.cover 1 2 3 6))) (.tip (.cover 1 2 3 5)))
private theorem t9_434OK : treeOK shape9_25 66 1 t9_434=true := by decide

private def t9_432 : Tree 9 := .split 6 t9_433 t9_434
private theorem t9_432OK : treeOK shape9_25 2 1 t9_432=true := by
  change (treeOK shape9_25 2 (1 ||| 2^6) t9_433 && treeOK shape9_25 (2 ||| 2^6) 1 t9_434)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_433OK,t9_434OK⟩

private def t9_430 : Tree 9 := .split 1 t9_431 t9_432
private theorem t9_430OK : treeOK shape9_25 0 1 t9_430=true := by
  change (treeOK shape9_25 0 (1 ||| 2^1) t9_431 && treeOK shape9_25 (0 ||| 2^1) 1 t9_432)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_431OK,t9_432OK⟩

private def t9_436 : Tree 9 := (.split 6 (.tip (.small 1)) (.split 7 (.split 18 (.split 2 (.split 8 (.split 9 (.tip (.cover 1 3 6 7)) (.tip (.cover 1 2 4 7))) (.tip (.cover 1 2 4 6))) (.split 3 (.split 4 (.tip (.cover 1 2 6 7)) (.tip (.cover 1 3 5 7))) (.tip (.cover 1 3 5 6)))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 2 4 5))))
private theorem t9_436OK : treeOK shape9_25 1 2 t9_436=true := by decide

private def t9_438 : Tree 9 := (.split 2 (.split 18 (.split 3 (.split 4 (.tip (.cover 1 2 6 7)) (.tip (.cover 1 3 4 7))) (.tip (.cover 1 3 4 6))) (.tip (.cover 1 3 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t9_438OK : treeOK shape9_25 3 64 t9_438=true := by decide

private def t9_439 : Tree 9 := (.split 2 (.split 8 (.split 13 (.split 3 (.tip (.cover 1 2 3 6)) (.tip (.cover 1 3 4 6))) (.tip (.cover 1 2 3 7))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t9_439OK : treeOK shape9_25 67 0 t9_439=true := by decide

private def t9_437 : Tree 9 := .split 6 t9_438 t9_439
private theorem t9_437OK : treeOK shape9_25 3 0 t9_437=true := by
  change (treeOK shape9_25 3 (0 ||| 2^6) t9_438 && treeOK shape9_25 (3 ||| 2^6) 0 t9_439)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_438OK,t9_439OK⟩

private def t9_435 : Tree 9 := .split 1 t9_436 t9_437
private theorem t9_435OK : treeOK shape9_25 1 0 t9_435=true := by
  change (treeOK shape9_25 1 (0 ||| 2^1) t9_436 && treeOK shape9_25 (1 ||| 2^1) 0 t9_437)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_436OK,t9_437OK⟩

private def t9_429 : Tree 9 := .split 0 t9_430 t9_435
private theorem t9_429OK : treeOK shape9_25 0 0 t9_429=true := by
  change (treeOK shape9_25 0 (0 ||| 2^0) t9_430 && treeOK shape9_25 (0 ||| 2^0) 0 t9_435)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_430OK,t9_435OK⟩

private def shape9_26 : Shape := ⟨true,7,5,3⟩
private def t9_443 : Tree 9 := (.split 15 (.split 16 (.split 18 (.tip (.cover 1 5 6 7)) (.tip (.cover 2 3 4 6))) (.tip (.cover 2 3 4 5))) (.tip (.cover 2 3 4 5)))
private theorem t9_443OK : treeOK shape9_26 0 67 t9_443=true := by decide

private def t9_448 : Tree 9 := (.split 5 (.split 7 (.split 8 (.tip (.cover 1 3 5 6)) (.split 12 (.split 16 (.tip (.cover 1 3 5 7)) (.tip (.cover 1 4 5 6))) (.tip (.cover 1 3 5 6)))) (.split 8 (.split 11 (.split 18 (.tip (.cover 1 3 6 7)) (.tip (.cover 1 4 5 6))) (.tip (.cover 1 3 5 6))) (.tip (.cover 1 4 5 6)))) (.tip (.cover 1 2 3 7)))
private theorem t9_448OK : treeOK shape9_26 64 49683 t9_448=true := by decide

private def t9_449 : Tree 9 := (.split 5 (.tip (.cover 0 2 4 8)) (.tip (.cover 3 4 7 8)))
private theorem t9_449OK : treeOK shape9_26 80 49667 t9_449=true := by decide

private def t9_447 : Tree 9 := .split 4 t9_448 t9_449
private theorem t9_447OK : treeOK shape9_26 64 49667 t9_447=true := by
  change (treeOK shape9_26 64 (49667 ||| 2^4) t9_448 && treeOK shape9_26 (64 ||| 2^4) 49667 t9_449)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_448OK,t9_449OK⟩

private def t9_450 : Tree 9 := (.split 4 (.split 10 (.split 11 (.split 12 (.tip (.cover 1 4 5 6)) (.tip (.cover 2 3 6 8))) (.tip (.cover 2 3 5 8))) (.split 11 (.split 12 (.tip (.cover 1 4 5 6)) (.tip (.cover 2 3 6 8))) (.tip (.cover 2 3 5 8)))) (.tip (.cover 0 2 3 8)))
private theorem t9_450OK : treeOK shape9_26 16448 33283 t9_450=true := by decide

private def t9_446 : Tree 9 := .split 14 t9_447 t9_450
private theorem t9_446OK : treeOK shape9_26 64 33283 t9_446=true := by
  change (treeOK shape9_26 64 (33283 ||| 2^14) t9_447 && treeOK shape9_26 (64 ||| 2^14) 33283 t9_450)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_447OK,t9_450OK⟩

private def t9_452 : Tree 9 := (.split 13 (.split 4 (.split 5 (.split 7 (.split 8 (.tip (.cover 1 3 5 6)) (.tip (.cover 1 4 6 7))) (.tip (.cover 1 4 5 7))) (.tip (.cover 1 2 4 7))) (.split 5 (.tip (.cover 0 2 3 8)) (.tip (.cover 0 1 2 3)))) (.split 16 (.split 18 (.tip (.cover 1 5 6 7)) (.tip (.cover 1 3 4 6))) (.tip (.cover 1 3 4 5))))
private theorem t9_452OK : treeOK shape9_26 576 33795 t9_452=true := by decide

private def t9_453 : Tree 9 := (.tip (.cover 2 4 7 8))
private theorem t9_453OK : treeOK shape9_26 1600 32771 t9_453=true := by decide

private def t9_451 : Tree 9 := .split 10 t9_452 t9_453
private theorem t9_451OK : treeOK shape9_26 576 32771 t9_451=true := by
  change (treeOK shape9_26 576 (32771 ||| 2^10) t9_452 && treeOK shape9_26 (576 ||| 2^10) 32771 t9_453)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_452OK,t9_453OK⟩

private def t9_445 : Tree 9 := .split 9 t9_446 t9_451
private theorem t9_445OK : treeOK shape9_26 64 32771 t9_445=true := by
  change (treeOK shape9_26 64 (32771 ||| 2^9) t9_446 && treeOK shape9_26 (64 ||| 2^9) 32771 t9_451)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_446OK,t9_451OK⟩

private def t9_454 : Tree 9 := (.tip (.cover 2 3 4 5))
private theorem t9_454OK : treeOK shape9_26 32832 3 t9_454=true := by decide

private def t9_444 : Tree 9 := .split 15 t9_445 t9_454
private theorem t9_444OK : treeOK shape9_26 64 3 t9_444=true := by
  change (treeOK shape9_26 64 (3 ||| 2^15) t9_445 && treeOK shape9_26 (64 ||| 2^15) 3 t9_454)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_445OK,t9_454OK⟩

private def t9_442 : Tree 9 := .split 6 t9_443 t9_444
private theorem t9_442OK : treeOK shape9_26 0 3 t9_442=true := by
  change (treeOK shape9_26 0 (3 ||| 2^6) t9_443 && treeOK shape9_26 (0 ||| 2^6) 3 t9_444)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_443OK,t9_444OK⟩

private def t9_461 : Tree 9 := (.split 3 (.tip (.cover 1 2 5 6)) (.split 10 (.split 12 (.split 16 (.tip (.cover 1 2 5 7)) (.tip (.cover 1 4 5 6))) (.tip (.cover 1 2 5 6))) (.tip (.cover 1 2 3 7))))
private theorem t9_461OK : treeOK shape9_26 2 49749 t9_461=true := by decide

private def t9_462 : Tree 9 := (.split 3 (.split 10 (.split 11 (.split 18 (.tip (.cover 1 2 6 7)) (.tip (.cover 1 4 5 6))) (.tip (.cover 1 2 5 6))) (.tip (.cover 1 2 3 7))) (.tip (.cover 1 4 5 6)))
private theorem t9_462OK : treeOK shape9_26 6 49745 t9_462=true := by decide

private def t9_460 : Tree 9 := .split 2 t9_461 t9_462
private theorem t9_460OK : treeOK shape9_26 2 49745 t9_460=true := by
  change (treeOK shape9_26 2 (49745 ||| 2^2) t9_461 && treeOK shape9_26 (2 ||| 2^2) 49745 t9_462)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_461OK,t9_462OK⟩

private def t9_463 : Tree 9 := (.split 10 (.tip (.cover 0 3 4 8)) (.tip (.cover 2 4 7 8)))
private theorem t9_463OK : treeOK shape9_26 514 49233 t9_463=true := by decide

private def t9_459 : Tree 9 := .split 9 t9_460 t9_463
private theorem t9_459OK : treeOK shape9_26 2 49233 t9_459=true := by
  change (treeOK shape9_26 2 (49233 ||| 2^9) t9_460 && treeOK shape9_26 (2 ||| 2^9) 49233 t9_463)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_460OK,t9_463OK⟩

private def t9_464 : Tree 9 := (.split 5 (.split 9 (.split 11 (.split 12 (.tip (.cover 1 4 5 6)) (.tip (.cover 2 3 6 8))) (.tip (.cover 2 3 5 8))) (.tip (.cover 0 2 3 8))) (.split 9 (.split 11 (.split 12 (.tip (.cover 1 4 5 6)) (.tip (.cover 2 3 6 8))) (.tip (.cover 2 3 5 8))) (.tip (.cover 0 2 3 4))))
private theorem t9_464OK : treeOK shape9_26 16386 32849 t9_464=true := by decide

private def t9_458 : Tree 9 := .split 14 t9_459 t9_464
private theorem t9_458OK : treeOK shape9_26 2 32849 t9_458=true := by
  change (treeOK shape9_26 2 (32849 ||| 2^14) t9_459 && treeOK shape9_26 (2 ||| 2^14) 32849 t9_464)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_459OK,t9_464OK⟩

private def t9_465 : Tree 9 := (.split 5 (.split 13 (.split 9 (.split 2 (.split 3 (.tip (.cover 1 2 5 6)) (.tip (.cover 1 4 6 7))) (.tip (.cover 1 4 5 7))) (.split 10 (.tip (.cover 0 2 3 8)) (.tip (.cover 0 1 2 3)))) (.split 16 (.split 18 (.tip (.cover 1 5 6 7)) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 2 4 5)))) (.tip (.cover 3 4 7 8)))
private theorem t9_465OK : treeOK shape9_26 18 32833 t9_465=true := by decide

private def t9_457 : Tree 9 := .split 4 t9_458 t9_465
private theorem t9_457OK : treeOK shape9_26 2 32833 t9_457=true := by
  change (treeOK shape9_26 2 (32833 ||| 2^4) t9_458 && treeOK shape9_26 (2 ||| 2^4) 32833 t9_465)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_458OK,t9_465OK⟩

private def t9_466 : Tree 9 := (.tip (.cover 2 3 4 5))
private theorem t9_466OK : treeOK shape9_26 32770 65 t9_466=true := by decide

private def t9_456 : Tree 9 := .split 15 t9_457 t9_466
private theorem t9_456OK : treeOK shape9_26 2 65 t9_456=true := by
  change (treeOK shape9_26 2 (65 ||| 2^15) t9_457 && treeOK shape9_26 (2 ||| 2^15) 65 t9_466)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_457OK,t9_466OK⟩

private def t9_467 : Tree 9 := (.split 11 (.split 18 (.split 5 (.split 10 (.tip (.cover 0 2 3 8)) (.split 7 (.tip (.cover 1 3 4 5)) (.tip (.cover 2 4 5 8)))) (.split 10 (.split 2 (.tip (.cover 1 2 4 5)) (.tip (.cover 3 4 5 8))) (.tip (.cover 0 1 2 3)))) (.tip (.cover 1 2 3 6))) (.tip (.cover 1 2 3 5)))
private theorem t9_467OK : treeOK shape9_26 66 1 t9_467=true := by decide

private def t9_455 : Tree 9 := .split 6 t9_456 t9_467
private theorem t9_455OK : treeOK shape9_26 2 1 t9_455=true := by
  change (treeOK shape9_26 2 (1 ||| 2^6) t9_456 && treeOK shape9_26 (2 ||| 2^6) 1 t9_467)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_456OK,t9_467OK⟩

private def t9_441 : Tree 9 := .split 1 t9_442 t9_455
private theorem t9_441OK : treeOK shape9_26 0 1 t9_441=true := by
  change (treeOK shape9_26 0 (1 ||| 2^1) t9_442 && treeOK shape9_26 (0 ||| 2^1) 1 t9_455)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_442OK,t9_455OK⟩

private def t9_475 : Tree 9 := (.split 3 (.tip (.cover 1 2 5 6)) (.split 8 (.split 14 (.split 16 (.tip (.cover 1 2 5 7)) (.tip (.cover 1 3 5 6))) (.tip (.cover 1 2 4 7))) (.tip (.cover 1 2 5 6))))
private theorem t9_475OK : treeOK shape9_26 1 42070 t9_475=true := by decide

private def t9_476 : Tree 9 := (.split 3 (.split 7 (.split 14 (.split 18 (.tip (.cover 1 2 6 7)) (.tip (.cover 1 3 5 6))) (.tip (.cover 1 2 4 7))) (.tip (.cover 1 2 5 6))) (.tip (.cover 1 3 5 6)))
private theorem t9_476OK : treeOK shape9_26 5 42066 t9_476=true := by decide

private def t9_474 : Tree 9 := .split 2 t9_475 t9_476
private theorem t9_474OK : treeOK shape9_26 1 42066 t9_474=true := by
  change (treeOK shape9_26 1 (42066 ||| 2^2) t9_475 && treeOK shape9_26 (1 ||| 2^2) 42066 t9_476)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_475OK,t9_476OK⟩

private def t9_477 : Tree 9 := (.split 14 (.tip (.cover 0 3 4 8)) (.tip (.cover 2 3 7 8)))
private theorem t9_477OK : treeOK shape9_26 8193 33874 t9_477=true := by decide

private def t9_473 : Tree 9 := .split 13 t9_474 t9_477
private theorem t9_473OK : treeOK shape9_26 1 33874 t9_473=true := by
  change (treeOK shape9_26 1 (33874 ||| 2^13) t9_474 && treeOK shape9_26 (1 ||| 2^13) 33874 t9_477)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_474OK,t9_477OK⟩

private def t9_478 : Tree 9 := (.split 5 (.split 7 (.split 8 (.tip (.cover 1 3 5 6)) (.tip (.cover 2 4 6 8))) (.tip (.cover 2 4 5 8))) (.split 7 (.split 8 (.tip (.cover 1 3 5 6)) (.tip (.cover 2 4 6 8))) (.tip (.cover 2 4 5 8))))
private theorem t9_478OK : treeOK shape9_26 1025 32850 t9_478=true := by decide

private def t9_472 : Tree 9 := .split 10 t9_473 t9_478
private theorem t9_472OK : treeOK shape9_26 1 32850 t9_472=true := by
  change (treeOK shape9_26 1 (32850 ||| 2^10) t9_473 && treeOK shape9_26 (1 ||| 2^10) 32850 t9_478)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_473OK,t9_478OK⟩

private def t9_479 : Tree 9 := (.split 5 (.split 9 (.split 13 (.split 2 (.split 3 (.tip (.cover 1 2 5 6)) (.tip (.cover 1 3 6 7))) (.tip (.cover 1 3 5 7))) (.split 14 (.tip (.cover 0 2 4 8)) (.tip (.cover 0 1 2 4)))) (.split 16 (.split 18 (.tip (.cover 1 5 6 7)) (.tip (.cover 1 2 3 6))) (.tip (.cover 1 2 3 5)))) (.tip (.cover 3 4 7 8)))
private theorem t9_479OK : treeOK shape9_26 17 32834 t9_479=true := by decide

private def t9_471 : Tree 9 := .split 4 t9_472 t9_479
private theorem t9_471OK : treeOK shape9_26 1 32834 t9_471=true := by
  change (treeOK shape9_26 1 (32834 ||| 2^4) t9_472 && treeOK shape9_26 (1 ||| 2^4) 32834 t9_479)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_472OK,t9_479OK⟩

private def t9_480 : Tree 9 := (.tip (.cover 2 3 4 5))
private theorem t9_480OK : treeOK shape9_26 32769 66 t9_480=true := by decide

private def t9_470 : Tree 9 := .split 15 t9_471 t9_480
private theorem t9_470OK : treeOK shape9_26 1 66 t9_470=true := by
  change (treeOK shape9_26 1 (66 ||| 2^15) t9_471 && treeOK shape9_26 (1 ||| 2^15) 66 t9_480)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_471OK,t9_480OK⟩

private def t9_481 : Tree 9 := (.split 7 (.split 18 (.split 5 (.split 14 (.tip (.cover 0 2 4 8)) (.split 8 (.split 9 (.tip (.cover 1 3 6 7)) (.tip (.cover 1 2 4 7))) (.tip (.cover 1 2 4 6)))) (.split 10 (.split 2 (.tip (.cover 1 2 3 5)) (.tip (.cover 3 4 5 8))) (.tip (.cover 0 2 4 8)))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 2 4 5)))
private theorem t9_481OK : treeOK shape9_26 65 2 t9_481=true := by decide

private def t9_469 : Tree 9 := .split 6 t9_470 t9_481
private theorem t9_469OK : treeOK shape9_26 1 2 t9_469=true := by
  change (treeOK shape9_26 1 (2 ||| 2^6) t9_470 && treeOK shape9_26 (1 ||| 2^6) 2 t9_481)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_470OK,t9_481OK⟩

private def t9_484 : Tree 9 := (.split 18 (.split 5 (.split 7 (.split 11 (.tip (.cover 1 3 4 5)) (.split 12 (.split 13 (.tip (.cover 1 4 6 7)) (.tip (.cover 1 2 5 7))) (.tip (.cover 1 2 5 6)))) (.split 8 (.split 9 (.tip (.cover 1 3 6 7)) (.tip (.cover 1 2 5 7))) (.tip (.cover 1 2 5 6)))) (.tip (.cover 0 3 4 8))) (.tip (.cover 1 3 4 6)))
private theorem t9_484OK : treeOK shape9_26 3 68 t9_484=true := by decide

private def t9_485 : Tree 9 := (.tip (.cover 1 3 4 5))
private theorem t9_485OK : treeOK shape9_26 7 64 t9_485=true := by decide

private def t9_483 : Tree 9 := .split 2 t9_484 t9_485
private theorem t9_483OK : treeOK shape9_26 3 64 t9_483=true := by
  change (treeOK shape9_26 3 (64 ||| 2^2) t9_484 && treeOK shape9_26 (3 ||| 2^2) 64 t9_485)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_484OK,t9_485OK⟩

private def t9_486 : Tree 9 := (.split 2 (.split 8 (.split 13 (.split 5 (.split 7 (.tip (.cover 1 2 3 5)) (.tip (.cover 1 2 4 5))) (.tip (.cover 0 3 4 8))) (.tip (.cover 1 2 3 7))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t9_486OK : treeOK shape9_26 67 0 t9_486=true := by decide

private def t9_482 : Tree 9 := .split 6 t9_483 t9_486
private theorem t9_482OK : treeOK shape9_26 3 0 t9_482=true := by
  change (treeOK shape9_26 3 (0 ||| 2^6) t9_483 && treeOK shape9_26 (3 ||| 2^6) 0 t9_486)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_483OK,t9_486OK⟩

private def t9_468 : Tree 9 := .split 1 t9_469 t9_482
private theorem t9_468OK : treeOK shape9_26 1 0 t9_468=true := by
  change (treeOK shape9_26 1 (0 ||| 2^1) t9_469 && treeOK shape9_26 (1 ||| 2^1) 0 t9_482)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_469OK,t9_482OK⟩

private def t9_440 : Tree 9 := .split 0 t9_441 t9_468
private theorem t9_440OK : treeOK shape9_26 0 0 t9_440=true := by
  change (treeOK shape9_26 0 (0 ||| 2^0) t9_441 && treeOK shape9_26 (0 ||| 2^0) 0 t9_468)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_441OK,t9_468OK⟩

private def shape9_27 : Shape := ⟨true,8,4,3⟩
private def t9_489 : Tree 9 := (.tip (.small 1))
private theorem t9_489OK : treeOK shape9_27 0 3 t9_489=true := by decide

private def t9_490 : Tree 9 := (.split 6 (.tip (.small 1)) (.split 11 (.split 18 (.split 5 (.split 10 (.tip (.cover 1 2 3 8)) (.split 7 (.tip (.cover 1 3 4 5)) (.tip (.cover 1 2 5 8)))) (.split 10 (.split 2 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 3 5 8))) (.tip (.cover 0 1 4 8)))) (.tip (.cover 1 2 3 6))) (.tip (.cover 1 2 3 5))))
private theorem t9_490OK : treeOK shape9_27 2 1 t9_490=true := by decide

private def t9_488 : Tree 9 := .split 1 t9_489 t9_490
private theorem t9_488OK : treeOK shape9_27 0 1 t9_488=true := by
  change (treeOK shape9_27 0 (1 ||| 2^1) t9_489 && treeOK shape9_27 (0 ||| 2^1) 1 t9_490)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_489OK,t9_490OK⟩

private def t9_493 : Tree 9 := (.tip (.small 1))
private theorem t9_493OK : treeOK shape9_27 1 66 t9_493=true := by decide

private def t9_494 : Tree 9 := (.split 7 (.split 18 (.split 5 (.split 14 (.tip (.cover 1 2 4 8)) (.split 8 (.split 9 (.tip (.cover 1 3 6 7)) (.tip (.cover 1 2 4 7))) (.tip (.cover 1 2 4 6)))) (.split 10 (.split 17 (.tip (.cover 1 3 5 8)) (.tip (.cover 0 1 3 8))) (.tip (.cover 1 2 4 8)))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 2 4 5)))
private theorem t9_494OK : treeOK shape9_27 65 2 t9_494=true := by decide

private def t9_492 : Tree 9 := .split 6 t9_493 t9_494
private theorem t9_492OK : treeOK shape9_27 1 2 t9_492=true := by
  change (treeOK shape9_27 1 (2 ||| 2^6) t9_493 && treeOK shape9_27 (1 ||| 2^6) 2 t9_494)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_493OK,t9_494OK⟩

private def t9_496 : Tree 9 := (.split 2 (.split 18 (.split 5 (.split 17 (.tip (.cover 1 2 5 8)) (.tip (.cover 1 3 4 5))) (.tip (.cover 1 3 4 8))) (.tip (.cover 1 3 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t9_496OK : treeOK shape9_27 3 64 t9_496=true := by decide

private def t9_497 : Tree 9 := (.split 2 (.split 8 (.split 13 (.split 5 (.split 17 (.tip (.cover 1 2 5 8)) (.tip (.cover 1 2 3 5))) (.tip (.cover 1 3 4 8))) (.tip (.cover 1 2 3 7))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t9_497OK : treeOK shape9_27 67 0 t9_497=true := by decide

private def t9_495 : Tree 9 := .split 6 t9_496 t9_497
private theorem t9_495OK : treeOK shape9_27 3 0 t9_495=true := by
  change (treeOK shape9_27 3 (0 ||| 2^6) t9_496 && treeOK shape9_27 (3 ||| 2^6) 0 t9_497)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_496OK,t9_497OK⟩

private def t9_491 : Tree 9 := .split 1 t9_492 t9_495
private theorem t9_491OK : treeOK shape9_27 1 0 t9_491=true := by
  change (treeOK shape9_27 1 (0 ||| 2^1) t9_492 && treeOK shape9_27 (1 ||| 2^1) 0 t9_495)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_492OK,t9_495OK⟩

private def t9_487 : Tree 9 := .split 0 t9_488 t9_491
private theorem t9_487OK : treeOK shape9_27 0 0 t9_487=true := by
  change (treeOK shape9_27 0 (0 ||| 2^0) t9_488 && treeOK shape9_27 (0 ||| 2^0) 0 t9_491)=true
  rw [Bool.and_eq_true]
  exact ⟨t9_488OK,t9_491OK⟩

def forms9 : Fin 28 → Shape := ![⟨false,4,4,1⟩,⟨false,4,4,2⟩,⟨false,5,4,2⟩,⟨false,4,4,3⟩,⟨false,5,4,3⟩,⟨false,5,5,3⟩,⟨false,6,4,3⟩,⟨true,4,4,0⟩,⟨true,5,4,0⟩,⟨true,4,4,1⟩,⟨true,5,4,1⟩,⟨true,5,5,1⟩,⟨true,6,4,1⟩,⟨true,4,4,2⟩,⟨true,5,4,2⟩,⟨true,5,5,2⟩,⟨true,6,4,2⟩,⟨true,6,5,2⟩,⟨true,7,4,2⟩,⟨true,4,4,3⟩,⟨true,5,4,3⟩,⟨true,5,5,3⟩,⟨true,6,4,3⟩,⟨true,6,5,3⟩,⟨true,6,6,3⟩,⟨true,7,4,3⟩,⟨true,7,5,3⟩,⟨true,8,4,3⟩]

theorem check9 (i : Fin 28) (b : Nat→Bool)
    (H : Ranked (n:=9) (adj (forms9 i) b)) :
    ∃ a b' c d : Fin 9, Effective (adj (forms9 i) b) (adj (forms9 i) b) a b' c d := by
  fin_cases i
  · exact (checked_tree shape9_0 b H t9_0 t9_0OK)
  · exact (checked_tree shape9_1 b H t9_9 t9_9OK)
  · exact (checked_tree shape9_2 b H t9_14 t9_14OK)
  · exact (checked_tree shape9_3 b H t9_39 t9_39OK)
  · exact (checked_tree shape9_4 b H t9_42 t9_42OK)
  · exact (checked_tree shape9_5 b H t9_49 t9_49OK)
  · exact (checked_tree shape9_6 b H t9_80 t9_80OK)
  · exact (checked_tree shape9_7 b H t9_87 t9_87OK)
  · exact (checked_tree shape9_8 b H t9_88 t9_88OK)
  · exact (checked_tree shape9_9 b H t9_89 t9_89OK)
  · exact (checked_tree shape9_10 b H t9_90 t9_90OK)
  · exact (checked_tree shape9_11 b H t9_91 t9_91OK)
  · exact (checked_tree shape9_12 b H t9_122 t9_122OK)
  · exact (checked_tree shape9_13 b H t9_123 t9_123OK)
  · exact (checked_tree shape9_14 b H t9_124 t9_124OK)
  · exact (checked_tree shape9_15 b H t9_131 t9_131OK)
  · exact (checked_tree shape9_16 b H t9_180 t9_180OK)
  · exact (checked_tree shape9_17 b H t9_189 t9_189OK)
  · exact (checked_tree shape9_18 b H t9_248 t9_248OK)
  · exact (checked_tree shape9_19 b H t9_263 t9_263OK)
  · exact (checked_tree shape9_20 b H t9_270 t9_270OK)
  · exact (checked_tree shape9_21 b H t9_275 t9_275OK)
  · exact (checked_tree shape9_22 b H t9_318 t9_318OK)
  · exact (checked_tree shape9_23 b H t9_329 t9_329OK)
  · exact (checked_tree shape9_24 b H t9_378 t9_378OK)
  · exact (checked_tree shape9_25 b H t9_429 t9_429OK)
  · exact (checked_tree shape9_26 b H t9_440 t9_440OK)
  · exact (checked_tree shape9_27 b H t9_487 t9_487OK)
#print axioms check9
end Graffiti384b.SmallPalette
