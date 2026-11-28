import SmallPalette384b
import Mathlib.Tactic.FinCases
namespace Graffiti384b.SmallPalette
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 500000

private def shape7_0 : Shape := ⟨false,4,4,3⟩
private def t7_1 : Tree 7 := (.split 1 (.tip (.small 0)) (.split 4 (.tip (.small 0)) (.split 7 (.tip (.small 0)) (.tip (.cover 1 2 3 5)))))
private theorem t7_1OK : treeOK shape7_0 0 1 t7_1=true := by decide

private def t7_2 : Tree 7 := (.split 1 (.split 4 (.tip (.small 0)) (.split 5 (.tip (.small 0)) (.tip (.cover 1 2 4 5)))) (.split 4 (.split 2 (.tip (.small 0)) (.tip (.cover 1 3 4 5))) (.split 2 (.split 6 (.split 7 (.tip (.small 0)) (.tip (.cover 1 2 3 5))) (.tip (.cover 0 2 4 6))) (.tip (.cover 1 3 4 5)))))
private theorem t7_2OK : treeOK shape7_0 1 0 t7_2=true := by decide

private def t7_0 : Tree 7 := .split 0 t7_1 t7_2
private theorem t7_0OK : treeOK shape7_0 0 0 t7_0=true := by
  change (treeOK shape7_0 0 (0 ||| 2^0) t7_1 && treeOK shape7_0 (0 ||| 2^0) 0 t7_2)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_1OK,t7_2OK⟩

private def shape7_1 : Shape := ⟨true,4,4,1⟩
private def t7_3 : Tree 7 := (.tip (.small 0))
private theorem t7_3OK : treeOK shape7_1 0 0 t7_3=true := by decide

private def shape7_2 : Shape := ⟨true,4,4,2⟩
private def t7_4 : Tree 7 := (.split 0 (.tip (.small 0)) (.split 1 (.tip (.small 0)) (.split 2 (.tip (.small 1)) (.split 4 (.tip (.small 0)) (.split 5 (.tip (.small 1)) (.tip (.cover 0 1 4 5)))))))
private theorem t7_4OK : treeOK shape7_2 0 0 t7_4=true := by decide

private def shape7_3 : Shape := ⟨true,5,4,2⟩
private def t7_6 : Tree 7 := (.tip (.small 1))
private theorem t7_6OK : treeOK shape7_3 0 1 t7_6=true := by decide

private def t7_9 : Tree 7 := (.split 3 (.tip (.small 1)) (.split 6 (.tip (.small 1)) (.split 2 (.tip (.cover 1 2 3 5)) (.split 4 (.tip (.cover 1 2 3 4)) (.tip (.cover 1 4 5 6))))))
private theorem t7_9OK : treeOK shape7_3 1 34 t7_9=true := by decide

private def t7_10 : Tree 7 := (.split 6 (.tip (.small 1)) (.split 2 (.split 4 (.split 3 (.tip (.small 1)) (.tip (.cover 1 2 3 4))) (.tip (.cover 1 2 4 5))) (.split 3 (.tip (.small 1)) (.tip (.cover 0 1 5 6)))))
private theorem t7_10OK : treeOK shape7_3 33 2 t7_10=true := by decide

private def t7_8 : Tree 7 := .split 5 t7_9 t7_10
private theorem t7_8OK : treeOK shape7_3 1 2 t7_8=true := by
  change (treeOK shape7_3 1 (2 ||| 2^5) t7_9 && treeOK shape7_3 (1 ||| 2^5) 2 t7_10)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_9OK,t7_10OK⟩

private def t7_11 : Tree 7 := (.split 2 (.split 4 (.split 3 (.tip (.small 1)) (.split 6 (.tip (.small 1)) (.split 5 (.tip (.cover 1 2 3 5)) (.tip (.cover 1 4 5 6))))) (.split 6 (.tip (.small 1)) (.split 3 (.tip (.small 1)) (.tip (.cover 0 1 4 6))))) (.tip (.cover 1 3 4 5)))
private theorem t7_11OK : treeOK shape7_3 3 0 t7_11=true := by decide

private def t7_7 : Tree 7 := .split 1 t7_8 t7_11
private theorem t7_7OK : treeOK shape7_3 1 0 t7_7=true := by
  change (treeOK shape7_3 1 (0 ||| 2^1) t7_8 && treeOK shape7_3 (1 ||| 2^1) 0 t7_11)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_8OK,t7_11OK⟩

private def t7_5 : Tree 7 := .split 0 t7_6 t7_7
private theorem t7_5OK : treeOK shape7_3 0 0 t7_5=true := by
  change (treeOK shape7_3 0 (0 ||| 2^0) t7_6 && treeOK shape7_3 (0 ||| 2^0) 0 t7_7)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_6OK,t7_7OK⟩

private def shape7_4 : Shape := ⟨true,4,4,3⟩
private def t7_13 : Tree 7 := (.split 1 (.tip (.small 0)) (.split 4 (.tip (.small 0)) (.split 7 (.tip (.cover 0 1 4 5)) (.split 8 (.tip (.cover 0 1 4 6)) (.split 9 (.tip (.cover 0 1 5 6)) (.tip (.cover 0 2 3 5)))))))
private theorem t7_13OK : treeOK shape7_4 0 1 t7_13=true := by decide

private def t7_15 : Tree 7 := (.split 4 (.tip (.small 0)) (.split 5 (.tip (.cover 0 1 3 5)) (.split 6 (.tip (.cover 0 1 3 6)) (.split 9 (.tip (.cover 0 1 5 6)) (.tip (.cover 0 2 4 5))))))
private theorem t7_15OK : treeOK shape7_4 1 2 t7_15=true := by decide

private def t7_16 : Tree 7 := (.split 4 (.split 2 (.tip (.cover 0 1 2 5)) (.split 3 (.tip (.cover 0 1 2 6)) (.split 9 (.tip (.cover 0 1 5 6)) (.tip (.cover 0 3 4 5))))) (.split 2 (.tip (.cover 0 1 2 5)) (.split 3 (.tip (.cover 0 1 2 6)) (.split 5 (.tip (.cover 0 1 3 5)) (.tip (.cover 0 1 4 5))))))
private theorem t7_16OK : treeOK shape7_4 3 0 t7_16=true := by decide

private def t7_14 : Tree 7 := .split 1 t7_15 t7_16
private theorem t7_14OK : treeOK shape7_4 1 0 t7_14=true := by
  change (treeOK shape7_4 1 (0 ||| 2^1) t7_15 && treeOK shape7_4 (1 ||| 2^1) 0 t7_16)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_15OK,t7_16OK⟩

private def t7_12 : Tree 7 := .split 0 t7_13 t7_14
private theorem t7_12OK : treeOK shape7_4 0 0 t7_12=true := by
  change (treeOK shape7_4 0 (0 ||| 2^0) t7_13 && treeOK shape7_4 (0 ||| 2^0) 0 t7_14)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_13OK,t7_14OK⟩

private def shape7_5 : Shape := ⟨true,5,4,3⟩
private def t7_19 : Tree 7 := (.tip (.small 1))
private theorem t7_19OK : treeOK shape7_5 0 3 t7_19=true := by decide

private def t7_21 : Tree 7 := (.tip (.small 1))
private theorem t7_21OK : treeOK shape7_5 2 17 t7_21=true := by decide

private def t7_22 : Tree 7 := (.split 7 (.split 2 (.split 5 (.tip (.rank 80)) (.split 6 (.tip (.rank 0)) (.split 8 (.tip (.cover 0 1 4 6)) (.tip (.cover 1 2 5 6))))) (.split 3 (.tip (.cover 0 1 2 6)) (.split 5 (.split 8 (.tip (.cover 0 1 4 6)) (.tip (.cover 1 3 5 6))) (.tip (.cover 0 1 4 5))))) (.tip (.cover 1 2 3 5)))
private theorem t7_22OK : treeOK shape7_5 18 1 t7_22=true := by decide

private def t7_20 : Tree 7 := .split 4 t7_21 t7_22
private theorem t7_20OK : treeOK shape7_5 2 1 t7_20=true := by
  change (treeOK shape7_5 2 (1 ||| 2^4) t7_21 && treeOK shape7_5 (2 ||| 2^4) 1 t7_22)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_21OK,t7_22OK⟩

private def t7_18 : Tree 7 := .split 1 t7_19 t7_20
private theorem t7_18OK : treeOK shape7_5 0 1 t7_18=true := by
  change (treeOK shape7_5 0 (1 ||| 2^1) t7_19 && treeOK shape7_5 (0 ||| 2^1) 1 t7_20)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_19OK,t7_20OK⟩

private def t7_24 : Tree 7 := (.split 4 (.tip (.small 1)) (.split 5 (.split 2 (.split 6 (.tip (.cover 0 1 3 6)) (.split 7 (.tip (.rank 72)) (.split 8 (.tip (.rank 0)) (.tip (.cover 1 2 5 6))))) (.split 3 (.tip (.cover 0 1 2 6)) (.split 6 (.tip (.cover 0 1 3 6)) (.tip (.cover 1 4 5 6))))) (.tip (.cover 1 2 4 5))))
private theorem t7_24OK : treeOK shape7_5 1 2 t7_24=true := by decide

private def t7_26 : Tree 7 := (.split 2 (.split 3 (.tip (.cover 0 1 2 6)) (.split 5 (.split 7 (.tip (.rank 68)) (.split 8 (.tip (.rank 0)) (.tip (.cover 1 3 5 6)))) (.split 6 (.tip (.cover 0 1 3 6)) (.tip (.cover 1 4 5 6))))) (.tip (.cover 1 3 4 5)))
private theorem t7_26OK : treeOK shape7_5 3 16 t7_26=true := by decide

private def t7_27 : Tree 7 := (.split 2 (.split 5 (.tip (.cover 1 2 3 5)) (.tip (.cover 1 2 4 5))) (.tip (.cover 1 3 4 5)))
private theorem t7_27OK : treeOK shape7_5 19 0 t7_27=true := by decide

private def t7_25 : Tree 7 := .split 4 t7_26 t7_27
private theorem t7_25OK : treeOK shape7_5 3 0 t7_25=true := by
  change (treeOK shape7_5 3 (0 ||| 2^4) t7_26 && treeOK shape7_5 (3 ||| 2^4) 0 t7_27)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_26OK,t7_27OK⟩

private def t7_23 : Tree 7 := .split 1 t7_24 t7_25
private theorem t7_23OK : treeOK shape7_5 1 0 t7_23=true := by
  change (treeOK shape7_5 1 (0 ||| 2^1) t7_24 && treeOK shape7_5 (1 ||| 2^1) 0 t7_25)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_24OK,t7_25OK⟩

private def t7_17 : Tree 7 := .split 0 t7_18 t7_23
private theorem t7_17OK : treeOK shape7_5 0 0 t7_17=true := by
  change (treeOK shape7_5 0 (0 ||| 2^0) t7_18 && treeOK shape7_5 (0 ||| 2^0) 0 t7_23)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_18OK,t7_23OK⟩

private def shape7_6 : Shape := ⟨true,5,5,3⟩
private def t7_31 : Tree 7 := (.split 9 (.tip (.rank 3)) (.tip (.cover 2 3 4 5)))
private theorem t7_31OK : treeOK shape7_6 0 19 t7_31=true := by decide

private def t7_33 : Tree 7 := (.split 8 (.split 2 (.split 3 (.tip (.rank 0)) (.tip (.cover 1 2 3 5))) (.split 3 (.tip (.cover 0 2 4 6)) (.tip (.cover 3 4 5 6)))) (.split 2 (.split 6 (.split 7 (.tip (.small 0)) (.tip (.rank 0))) (.split 7 (.tip (.small 0)) (.tip (.cover 2 3 5 6)))) (.tip (.cover 0 2 3 6))))
private theorem t7_33OK : treeOK shape7_6 16 35 t7_33=true := by decide

private def t7_34 : Tree 7 := (.split 6 (.split 7 (.split 2 (.split 3 (.tip (.rank 0)) (.tip (.cover 1 2 4 5))) (.split 3 (.tip (.cover 0 2 3 6)) (.tip (.cover 0 1 2 3)))) (.split 2 (.split 8 (.tip (.cover 0 3 4 6)) (.tip (.cover 2 3 5 6))) (.tip (.cover 0 2 3 4)))) (.tip (.cover 2 4 5 6)))
private theorem t7_34OK : treeOK shape7_6 48 3 t7_34=true := by decide

private def t7_32 : Tree 7 := .split 5 t7_33 t7_34
private theorem t7_32OK : treeOK shape7_6 16 3 t7_32=true := by
  change (treeOK shape7_6 16 (3 ||| 2^5) t7_33 && treeOK shape7_6 (16 ||| 2^5) 3 t7_34)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_33OK,t7_34OK⟩

private def t7_30 : Tree 7 := .split 4 t7_31 t7_32
private theorem t7_30OK : treeOK shape7_6 0 3 t7_30=true := by
  change (treeOK shape7_6 0 (3 ||| 2^4) t7_31 && treeOK shape7_6 (0 ||| 2^4) 3 t7_32)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_31OK,t7_32OK⟩

private def t7_38 : Tree 7 := (.split 5 (.split 3 (.tip (.rank 0)) (.split 6 (.tip (.rank 0)) (.tip (.cover 1 2 3 5)))) (.split 6 (.tip (.cover 0 3 4 6)) (.tip (.cover 2 4 5 6))))
private theorem t7_38OK : treeOK shape7_6 2 277 t7_38=true := by decide

private def t7_39 : Tree 7 := (.split 3 (.split 5 (.split 7 (.tip (.small 0)) (.tip (.rank 0))) (.tip (.cover 0 2 3 6))) (.split 5 (.split 7 (.tip (.small 0)) (.tip (.cover 2 3 5 6))) (.tip (.cover 0 2 3 4))))
private theorem t7_39OK : treeOK shape7_6 258 21 t7_39=true := by decide

private def t7_37 : Tree 7 := .split 8 t7_38 t7_39
private theorem t7_37OK : treeOK shape7_6 2 21 t7_37=true := by
  change (treeOK shape7_6 2 (21 ||| 2^8) t7_38 && treeOK shape7_6 (2 ||| 2^8) 21 t7_39)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_38OK,t7_39OK⟩

private def t7_40 : Tree 7 := (.split 3 (.split 7 (.split 5 (.split 6 (.tip (.rank 0)) (.tip (.cover 1 3 4 5))) (.split 6 (.tip (.cover 0 2 3 6)) (.tip (.cover 0 1 2 3)))) (.split 5 (.split 8 (.tip (.cover 0 2 4 6)) (.tip (.cover 2 3 5 6))) (.tip (.cover 0 2 3 4)))) (.tip (.cover 3 4 5 6)))
private theorem t7_40OK : treeOK shape7_6 6 17 t7_40=true := by decide

private def t7_36 : Tree 7 := .split 2 t7_37 t7_40
private theorem t7_36OK : treeOK shape7_6 2 17 t7_36=true := by
  change (treeOK shape7_6 2 (17 ||| 2^2) t7_37 && treeOK shape7_6 (2 ||| 2^2) 17 t7_40)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_37OK,t7_40OK⟩

private def t7_41 : Tree 7 := (.split 7 (.split 3 (.split 6 (.tip (.cover 0 2 3 6)) (.split 5 (.tip (.cover 1 3 4 5)) (.tip (.cover 2 4 5 6)))) (.split 6 (.split 2 (.tip (.cover 1 2 4 5)) (.tip (.cover 3 4 5 6))) (.tip (.cover 0 1 2 3)))) (.tip (.cover 1 2 3 5)))
private theorem t7_41OK : treeOK shape7_6 18 1 t7_41=true := by decide

private def t7_35 : Tree 7 := .split 4 t7_36 t7_41
private theorem t7_35OK : treeOK shape7_6 2 1 t7_35=true := by
  change (treeOK shape7_6 2 (1 ||| 2^4) t7_36 && treeOK shape7_6 (2 ||| 2^4) 1 t7_41)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_36OK,t7_41OK⟩

private def t7_29 : Tree 7 := .split 1 t7_30 t7_35
private theorem t7_29OK : treeOK shape7_6 0 1 t7_29=true := by
  change (treeOK shape7_6 0 (1 ||| 2^1) t7_30 && treeOK shape7_6 (0 ||| 2^1) 1 t7_35)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_30OK,t7_35OK⟩

private def t7_46 : Tree 7 := (.split 7 (.split 3 (.tip (.rank 0)) (.split 5 (.tip (.small 0)) (.tip (.rank 0)))) (.split 8 (.tip (.cover 0 3 4 6)) (.tip (.cover 2 3 5 6))))
private theorem t7_46OK : treeOK shape7_6 1 86 t7_46=true := by decide

private def t7_47 : Tree 7 := (.split 3 (.split 5 (.split 7 (.tip (.small 0)) (.tip (.cover 0 2 4 6))) (.tip (.cover 2 4 5 6))) (.split 5 (.tip (.cover 1 2 3 5)) (.tip (.cover 2 4 5 6))))
private theorem t7_47OK : treeOK shape7_6 65 22 t7_47=true := by decide

private def t7_45 : Tree 7 := .split 6 t7_46 t7_47
private theorem t7_45OK : treeOK shape7_6 1 22 t7_45=true := by
  change (treeOK shape7_6 1 (22 ||| 2^6) t7_46 && treeOK shape7_6 (1 ||| 2^6) 22 t7_47)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_46OK,t7_47OK⟩

private def t7_48 : Tree 7 := (.split 3 (.split 5 (.split 7 (.split 6 (.tip (.rank 0)) (.tip (.rank 0))) (.split 8 (.tip (.cover 0 2 4 6)) (.tip (.cover 0 1 2 4)))) (.split 6 (.tip (.cover 0 2 3 6)) (.tip (.cover 2 4 5 6)))) (.tip (.cover 3 4 5 6)))
private theorem t7_48OK : treeOK shape7_6 5 18 t7_48=true := by decide

private def t7_44 : Tree 7 := .split 2 t7_45 t7_48
private theorem t7_44OK : treeOK shape7_6 1 18 t7_44=true := by
  change (treeOK shape7_6 1 (18 ||| 2^2) t7_45 && treeOK shape7_6 (1 ||| 2^2) 18 t7_48)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_45OK,t7_48OK⟩

private def t7_49 : Tree 7 := (.split 5 (.split 3 (.split 8 (.tip (.cover 0 2 4 6)) (.split 6 (.split 7 (.tip (.rank 0)) (.tip (.cover 2 3 5 6))) (.tip (.cover 0 2 4 6)))) (.split 6 (.split 2 (.tip (.cover 1 2 3 5)) (.tip (.cover 3 4 5 6))) (.tip (.cover 0 2 4 6)))) (.tip (.cover 1 2 4 5)))
private theorem t7_49OK : treeOK shape7_6 17 2 t7_49=true := by decide

private def t7_43 : Tree 7 := .split 4 t7_44 t7_49
private theorem t7_43OK : treeOK shape7_6 1 2 t7_43=true := by
  change (treeOK shape7_6 1 (2 ||| 2^4) t7_44 && treeOK shape7_6 (1 ||| 2^4) 2 t7_49)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_44OK,t7_49OK⟩

private def t7_51 : Tree 7 := (.split 2 (.split 3 (.split 5 (.split 7 (.tip (.rank 66)) (.split 8 (.tip (.rank 0)) (.tip (.cover 2 3 5 6)))) (.split 6 (.tip (.cover 0 2 3 6)) (.tip (.cover 2 4 5 6)))) (.tip (.cover 0 3 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t7_51OK : treeOK shape7_6 3 16 t7_51=true := by decide

private def t7_52 : Tree 7 := (.split 2 (.split 6 (.split 7 (.tip (.rank 64)) (.tip (.cover 1 2 3 5))) (.tip (.cover 0 2 4 6))) (.tip (.cover 1 3 4 5)))
private theorem t7_52OK : treeOK shape7_6 19 0 t7_52=true := by decide

private def t7_50 : Tree 7 := .split 4 t7_51 t7_52
private theorem t7_50OK : treeOK shape7_6 3 0 t7_50=true := by
  change (treeOK shape7_6 3 (0 ||| 2^4) t7_51 && treeOK shape7_6 (3 ||| 2^4) 0 t7_52)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_51OK,t7_52OK⟩

private def t7_42 : Tree 7 := .split 1 t7_43 t7_50
private theorem t7_42OK : treeOK shape7_6 1 0 t7_42=true := by
  change (treeOK shape7_6 1 (0 ||| 2^1) t7_43 && treeOK shape7_6 (1 ||| 2^1) 0 t7_50)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_43OK,t7_50OK⟩

private def t7_28 : Tree 7 := .split 0 t7_29 t7_42
private theorem t7_28OK : treeOK shape7_6 0 0 t7_28=true := by
  change (treeOK shape7_6 0 (0 ||| 2^0) t7_29 && treeOK shape7_6 (0 ||| 2^0) 0 t7_42)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_29OK,t7_42OK⟩

private def shape7_7 : Shape := ⟨true,6,4,3⟩
private def t7_54 : Tree 7 := (.split 1 (.tip (.small 1)) (.split 4 (.tip (.small 1)) (.split 7 (.split 3 (.split 6 (.tip (.cover 1 2 3 6)) (.split 5 (.tip (.cover 1 3 4 5)) (.tip (.cover 1 2 5 6)))) (.split 6 (.split 2 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 3 5 6))) (.tip (.cover 0 1 4 6)))) (.tip (.cover 1 2 3 5)))))
private theorem t7_54OK : treeOK shape7_7 0 1 t7_54=true := by decide

private def t7_56 : Tree 7 := (.split 4 (.tip (.small 1)) (.split 5 (.split 3 (.split 8 (.tip (.cover 1 2 4 6)) (.split 6 (.split 7 (.tip (.cover 1 3 4 5)) (.tip (.cover 1 2 5 6))) (.tip (.cover 1 2 4 6)))) (.split 6 (.split 9 (.tip (.cover 1 3 5 6)) (.tip (.cover 0 1 3 6))) (.tip (.cover 1 2 4 6)))) (.tip (.cover 1 2 4 5))))
private theorem t7_56OK : treeOK shape7_7 1 2 t7_56=true := by decide

private def t7_57 : Tree 7 := (.split 4 (.split 2 (.split 3 (.split 9 (.tip (.cover 1 2 5 6)) (.tip (.cover 1 3 4 5))) (.tip (.cover 1 3 4 6))) (.tip (.cover 1 3 4 5))) (.split 2 (.split 6 (.split 7 (.tip (.cover 1 2 4 5)) (.tip (.cover 1 2 3 5))) (.tip (.cover 1 2 4 6))) (.tip (.cover 1 3 4 5))))
private theorem t7_57OK : treeOK shape7_7 3 0 t7_57=true := by decide

private def t7_55 : Tree 7 := .split 1 t7_56 t7_57
private theorem t7_55OK : treeOK shape7_7 1 0 t7_55=true := by
  change (treeOK shape7_7 1 (0 ||| 2^1) t7_56 && treeOK shape7_7 (1 ||| 2^1) 0 t7_57)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_56OK,t7_57OK⟩

private def t7_53 : Tree 7 := .split 0 t7_54 t7_55
private theorem t7_53OK : treeOK shape7_7 0 0 t7_53=true := by
  change (treeOK shape7_7 0 (0 ||| 2^0) t7_54 && treeOK shape7_7 (0 ||| 2^0) 0 t7_55)=true
  rw [Bool.and_eq_true]
  exact ⟨t7_54OK,t7_55OK⟩

def forms7 : Fin 8 → Shape := ![⟨false,4,4,3⟩,⟨true,4,4,1⟩,⟨true,4,4,2⟩,⟨true,5,4,2⟩,⟨true,4,4,3⟩,⟨true,5,4,3⟩,⟨true,5,5,3⟩,⟨true,6,4,3⟩]

theorem check7 (i : Fin 8) (b : Nat→Bool)
    (H : Ranked (n:=7) (adj (forms7 i) b)) :
    ∃ a b' c d : Fin 7, Effective (adj (forms7 i) b) (adj (forms7 i) b) a b' c d := by
  fin_cases i
  · exact (checked_tree shape7_0 b H t7_0 t7_0OK)
  · exact (checked_tree shape7_1 b H t7_3 t7_3OK)
  · exact (checked_tree shape7_2 b H t7_4 t7_4OK)
  · exact (checked_tree shape7_3 b H t7_5 t7_5OK)
  · exact (checked_tree shape7_4 b H t7_12 t7_12OK)
  · exact (checked_tree shape7_5 b H t7_17 t7_17OK)
  · exact (checked_tree shape7_6 b H t7_28 t7_28OK)
  · exact (checked_tree shape7_7 b H t7_53 t7_53OK)
#print axioms check7
end Graffiti384b.SmallPalette
