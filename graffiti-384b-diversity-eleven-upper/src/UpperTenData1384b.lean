import UpperTenModel384b

namespace Graffiti384b.DiversityEleven.CutTen
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private def t1m181T0 : Tree := (.split 21 (.split 44 (.split 19 (.split 36 (.split 28 (.split 40 (.tip (.scoreSmall 8)) (.split 15 (.tip (.scoreSmall 8)) (.tip (.noActive 8)))) (.split 40 (.split 15 (.tip (.scoreSmall 8)) (.tip (.noActive 8))) (.tip (.noActive 8)))) (.tip (.noActive 5))) (.tip (.noActive 2))) (.split 28 (.split 29 (.split 40 (.split 41 (.split 19 (.split 36 (.tip (.scoreSmall 5)) (.tip (.noActive 5))) (.tip (.noActive 2))) (.tip (.noActive 9))) (.tip (.noActive 8))) (.tip (.noActive 9))) (.tip (.noActive 8)))) (.tip (.noActive 2)))
private theorem t1m181T0OK : treeOK (staticMotif 1) 181 0 0 t1m181T0=true := by decide

theorem t1m181_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 1) bits) 181) :
    ∃ D,Cover (withBits (staticMotif 1) bits) D :=
  checked_tree (staticMotif 1) 181 bits H t1m181T0 t1m181T0OK

#print axioms t1m181_cover

private def t1m213T0 : Tree := (.split 20 (.split 21 (.split 39 (.split 44 (.split 28 (.split 15 (.tip (.scoreSmall 8)) (.split 37 (.tip (.scoreSmall 8)) (.tip (.noActive 8)))) (.split 15 (.split 37 (.tip (.scoreSmall 8)) (.tip (.noActive 8))) (.tip (.noActive 8)))) (.split 28 (.split 29 (.split 15 (.split 16 (.split 37 (.tip (.scoreSmall 8)) (.tip (.noActive 8))) (.tip (.noActive 9))) (.tip (.noActive 8))) (.tip (.noActive 9))) (.tip (.noActive 8)))) (.tip (.noActive 6))) (.tip (.noActive 2))) (.tip (.noActive 2)))
private theorem t1m213T0OK : treeOK (staticMotif 1) 213 0 0 t1m213T0=true := by decide

theorem t1m213_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 1) bits) 213) :
    ∃ D,Cover (withBits (staticMotif 1) bits) D :=
  checked_tree (staticMotif 1) 213 bits H t1m213T0 t1m213T0OK

#print axioms t1m213_cover

private def t1m229T5 : Tree := (.split 15 (.tip (.scoreSmall 8)) (.split 29 (.split 16 (.tip (.scoreSmall 9)) (.split 42 (.tip (.scoreSmall 8)) (.split 23 (.split 22 (.tip (.crossSmall 2)) (.split 43 (.tip (.crossSmall 9)) (.tip (.cover {0,1,5,7})))) (.tip (.cover {1,2,5,7}))))) (.split 16 (.split 42 (.tip (.scoreSmall 8)) (.split 43 (.split 23 (.tip (.crossSmall 9)) (.split 27 (.tip (.crossSmall 7)) (.split 40 (.tip (.scoreSmall 8)) (.split 41 (.tip (.crossSmall 9)) (.split 39 (.split 36 (.tip (.degreeSmall 7)) (.tip (.cover {1,2,6,7}))) (.tip (.cover {1,3,4,6}))))))) (.tip (.cover {1,3,5,7})))) (.tip (.noActive 9)))))
private theorem t1m229T5OK : treeOK (staticMotif 1) 229 0 17592458149888 t1m229T5=true := by decide

private def t1m229T8 : Tree := (.split 16 (.tip (.scoreSmall 9)) (.split 43 (.tip (.scoreSmall 9)) (.split 42 (.split 22 (.tip (.crossSmall 8)) (.split 27 (.tip (.crossSmall 7)) (.split 40 (.tip (.crossSmall 8)) (.split 36 (.split 39 (.tip (.degreeSmall 7)) (.split 41 (.tip (.scoreSmall 9)) (.tip (.cover {1,3,4,6})))) (.tip (.cover {1,2,6,7})))))) (.tip (.cover {1,3,5,7})))))
private theorem t1m229T8OK : treeOK (staticMotif 1) 229 268435456 17592726618112 t1m229T8=true := by decide

private def t1m229T11 : Tree := (.split 36 (.tip (.scoreSmall 7)) (.split 27 (.tip (.scoreSmall 7)) (.split 22 (.split 23 (.tip (.crossSmall 2)) (.split 42 (.tip (.crossSmall 8)) (.split 43 (.split 40 (.tip (.crossSmall 8)) (.tip (.cover {2,3,5,6}))) (.tip (.cover {1,3,5,7}))))) (.split 23 (.split 43 (.tip (.crossSmall 9)) (.split 42 (.split 40 (.tip (.crossSmall 8)) (.tip (.cover {1,3,6,7}))) (.tip (.cover {1,3,5,7})))) (.tip (.cover {1,2,3,5}))))))
private theorem t1m229T11OK : treeOK (staticMotif 1) 229 805306368 18141945626624 t1m229T11=true := by decide

private def t1m229T12 : Tree := (.split 36 (.split 27 (.tip (.scoreSmall 7)) (.split 40 (.tip (.scoreSmall 8)) (.split 23 (.split 22 (.tip (.crossSmall 2)) (.split 43 (.tip (.crossSmall 9)) (.split 42 (.split 41 (.tip (.crossSmall 9)) (.tip (.cover {0,3,4,6}))) (.tip (.cover {1,3,5,7}))))) (.tip (.cover {2,3,4,6}))))) (.tip (.noActive 7)))
private theorem t1m229T12OK : treeOK (staticMotif 1) 229 550561120256 17592189812736 t1m229T12=true := by decide

private def t1m229T10 : Tree := .split 39 t1m229T11 t1m229T12
private theorem t1m229T10OK : treeOK (staticMotif 1) 229 805306368 17592189812736 t1m229T10=true :=
  join (staticMotif 1) 229 39 805306368 17592189812736 18141945626624 550561120256 t1m229T11 t1m229T12 (by decide) (by decide) t1m229T11OK t1m229T12OK

private def t1m229T13 : Tree := (.tip (.noActive 9))
private theorem t1m229T13OK : treeOK (staticMotif 1) 229 805371904 17592189747200 t1m229T13=true := by decide

private def t1m229T9 : Tree := .split 16 t1m229T10 t1m229T13
private theorem t1m229T9OK : treeOK (staticMotif 1) 229 805306368 17592189747200 t1m229T9=true :=
  join (staticMotif 1) 229 16 805306368 17592189747200 17592189812736 805371904 t1m229T10 t1m229T13 (by decide) (by decide) t1m229T10OK t1m229T13OK

private def t1m229T7 : Tree := .split 29 t1m229T8 t1m229T9
private theorem t1m229T7OK : treeOK (staticMotif 1) 229 268435456 17592189747200 t1m229T7=true :=
  join (staticMotif 1) 229 29 268435456 17592189747200 17592726618112 805306368 t1m229T8 t1m229T9 (by decide) (by decide) t1m229T8OK t1m229T9OK

private def t1m229T14 : Tree := (.tip (.noActive 8))
private theorem t1m229T14OK : treeOK (staticMotif 1) 229 268468224 17592189714432 t1m229T14=true := by decide

private def t1m229T6 : Tree := .split 15 t1m229T7 t1m229T14
private theorem t1m229T6OK : treeOK (staticMotif 1) 229 268435456 17592189714432 t1m229T6=true :=
  join (staticMotif 1) 229 15 268435456 17592189714432 17592189747200 268468224 t1m229T7 t1m229T14 (by decide) (by decide) t1m229T7OK t1m229T14OK

private def t1m229T4 : Tree := .split 28 t1m229T5 t1m229T6
private theorem t1m229T4OK : treeOK (staticMotif 1) 229 0 17592189714432 t1m229T4=true :=
  join (staticMotif 1) 229 28 0 17592189714432 17592458149888 268435456 t1m229T5 t1m229T6 (by decide) (by decide) t1m229T5OK t1m229T6OK

private def t1m229T15 : Tree := (.tip (.noActive 2))
private theorem t1m229T15OK : treeOK (staticMotif 1) 229 524288 17592189190144 t1m229T15=true := by decide

private def t1m229T3 : Tree := .split 19 t1m229T4 t1m229T15
private theorem t1m229T3OK : treeOK (staticMotif 1) 229 0 17592189190144 t1m229T3=true :=
  join (staticMotif 1) 229 19 0 17592189190144 17592189714432 524288 t1m229T4 t1m229T15 (by decide) (by decide) t1m229T4OK t1m229T15OK

private def t1m229T16 : Tree := (.split 28 (.split 29 (.split 15 (.split 16 (.split 19 (.split 22 (.tip (.scoreSmall 2)) (.split 23 (.tip (.scoreSmall 2)) (.split 39 (.split 36 (.tip (.scoreSmall 7)) (.split 42 (.tip (.scoreSmall 7)) (.tip (.cover {1,2,5,8})))) (.split 36 (.split 40 (.tip (.scoreSmall 8)) (.split 41 (.tip (.scoreSmall 9)) (.split 27 (.split 42 (.tip (.crossSmall 7)) (.split 43 (.tip (.crossSmall 7)) (.tip (.cover {1,2,5,7})))) (.tip (.cover {2,3,4,6}))))) (.tip (.noActive 7)))))) (.tip (.noActive 2))) (.tip (.noActive 9))) (.tip (.noActive 8))) (.tip (.noActive 9))) (.tip (.noActive 8)))
private theorem t1m229T16OK : treeOK (staticMotif 1) 229 17592186044416 3145728 t1m229T16=true := by decide

private def t1m229T2 : Tree := .split 44 t1m229T3 t1m229T16
private theorem t1m229T2OK : treeOK (staticMotif 1) 229 0 3145728 t1m229T2=true :=
  join (staticMotif 1) 229 44 0 3145728 17592189190144 17592186044416 t1m229T3 t1m229T16 (by decide) (by decide) t1m229T3OK t1m229T16OK

private def t1m229T17 : Tree := (.tip (.noActive 2))
private theorem t1m229T17OK : treeOK (staticMotif 1) 229 1048576 2097152 t1m229T17=true := by decide

private def t1m229T1 : Tree := .split 20 t1m229T2 t1m229T17
private theorem t1m229T1OK : treeOK (staticMotif 1) 229 0 2097152 t1m229T1=true :=
  join (staticMotif 1) 229 20 0 2097152 3145728 1048576 t1m229T2 t1m229T17 (by decide) (by decide) t1m229T2OK t1m229T17OK

private def t1m229T18 : Tree := (.tip (.noActive 2))
private theorem t1m229T18OK : treeOK (staticMotif 1) 229 2097152 0 t1m229T18=true := by decide

private def t1m229T0 : Tree := .split 21 t1m229T1 t1m229T18
private theorem t1m229T0OK : treeOK (staticMotif 1) 229 0 0 t1m229T0=true :=
  join (staticMotif 1) 229 21 0 0 2097152 2097152 t1m229T1 t1m229T18 (by decide) (by decide) t1m229T1OK t1m229T18OK

theorem t1m229_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 1) bits) 229) :
    ∃ D,Cover (withBits (staticMotif 1) bits) D :=
  checked_tree (staticMotif 1) 229 bits H t1m229T0 t1m229T0OK

#print axioms t1m229_cover

private def t1m403T0 : Tree := (.tip (.noActive 1))
private theorem t1m403T0OK : treeOK (staticMotif 1) 403 0 0 t1m403T0=true := by decide

theorem t1m403_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 1) bits) 403) :
    ∃ D,Cover (withBits (staticMotif 1) bits) D :=
  checked_tree (staticMotif 1) 403 bits H t1m403T0 t1m403T0OK

#print axioms t1m403_cover

private def t1m419T6 : Tree := (.split 14 (.tip (.scoreSmall 9)) (.split 15 (.tip (.scoreSmall 9)) (.split 36 (.tip (.scoreSmall 9)) (.tip (.noActive 7)))))
private theorem t1m419T6OK : treeOK (staticMotif 1) 419 0 6597683183616 t1m419T6=true := by decide

private def t1m419T8 : Tree := (.split 36 (.tip (.scoreSmall 7)) (.split 40 (.tip (.scoreSmall 6)) (.split 15 (.split 37 (.tip (.scoreSmall 6)) (.split 39 (.tip (.scoreSmall 6)) (.split 27 (.tip (.scoreSmall 7)) (.split 44 (.split 43 (.tip (.crossSmall 9)) (.split 22 (.tip (.crossSmall 8)) (.tip (.cover {1,2,5,9})))) (.tip (.cover {1,3,5,8})))))) (.split 37 (.split 39 (.tip (.scoreSmall 6)) (.split 43 (.split 44 (.tip (.crossSmall 9)) (.split 21 (.tip (.crossSmall 7)) (.tip (.cover {1,2,5,9})))) (.tip (.cover {1,3,6,7})))) (.tip (.noActive 8))))))
private theorem t1m419T8OK : treeOK (staticMotif 1) 419 536870912 6597146329088 t1m419T8=true := by decide

private def t1m419T9 : Tree := (.split 36 (.split 37 (.tip (.scoreSmall 5)) (.split 15 (.split 39 (.tip (.scoreSmall 6)) (.split 40 (.tip (.scoreSmall 6)) (.split 44 (.split 43 (.tip (.crossSmall 9)) (.split 22 (.tip (.crossSmall 8)) (.tip (.cover {1,2,5,9})))) (.tip (.cover {1,3,6,8}))))) (.tip (.noActive 8)))) (.tip (.noActive 7)))
private theorem t1m419T9OK : treeOK (staticMotif 1) 419 536887296 6597146312704 t1m419T9=true := by decide

private def t1m419T7 : Tree := .split 14 t1m419T8 t1m419T9
private theorem t1m419T7OK : treeOK (staticMotif 1) 419 536870912 6597146312704 t1m419T7=true :=
  join (staticMotif 1) 419 14 536870912 6597146312704 6597146329088 536887296 t1m419T8 t1m419T9 (by decide) (by decide) t1m419T8OK t1m419T9OK

private def t1m419T5 : Tree := .split 29 t1m419T6 t1m419T7
private theorem t1m419T5OK : treeOK (staticMotif 1) 419 0 6597146312704 t1m419T5=true :=
  join (staticMotif 1) 419 29 0 6597146312704 6597683183616 536870912 t1m419T6 t1m419T7 (by decide) (by decide) t1m419T6OK t1m419T7OK

private def t1m419T12 : Tree := (.split 36 (.tip (.scoreSmall 7)) (.split 40 (.tip (.scoreSmall 6)) (.split 21 (.tip (.scoreSmall 7)) (.split 44 (.split 43 (.tip (.crossSmall 9)) (.split 15 (.split 37 (.tip (.degreeSmall 8)) (.split 39 (.tip (.scoreSmall 6)) (.split 22 (.tip (.crossSmall 8)) (.tip (.cover {1,2,5,7}))))) (.tip (.cover {1,2,6,7})))) (.tip (.cover {1,2,5,8}))))))
private theorem t1m419T12OK : treeOK (staticMotif 1) 419 8388608 6597674811392 t1m419T12=true := by decide

private def t1m419T13 : Tree := (.split 36 (.split 37 (.tip (.scoreSmall 5)) (.split 15 (.split 39 (.tip (.scoreSmall 6)) (.split 40 (.tip (.scoreSmall 6)) (.split 44 (.split 43 (.tip (.crossSmall 9)) (.split 21 (.tip (.scoreSmall 7)) (.split 22 (.tip (.crossSmall 8)) (.tip (.cover {1,2,5,7}))))) (.tip (.cover {1,2,6,8}))))) (.tip (.noActive 8)))) (.tip (.noActive 7)))
private theorem t1m419T13OK : treeOK (staticMotif 1) 419 8404992 6597674795008 t1m419T13=true := by decide

private def t1m419T11 : Tree := .split 14 t1m419T12 t1m419T13
private theorem t1m419T11OK : treeOK (staticMotif 1) 419 8388608 6597674795008 t1m419T11=true :=
  join (staticMotif 1) 419 14 8388608 6597674795008 6597674811392 8404992 t1m419T12 t1m419T13 (by decide) (by decide) t1m419T12OK t1m419T13OK

private def t1m419T14 : Tree := (.tip (.noActive 9))
private theorem t1m419T14OK : treeOK (staticMotif 1) 419 545259520 6597137924096 t1m419T14=true := by decide

private def t1m419T10 : Tree := .split 29 t1m419T11 t1m419T14
private theorem t1m419T10OK : treeOK (staticMotif 1) 419 8388608 6597137924096 t1m419T10=true :=
  join (staticMotif 1) 419 29 8388608 6597137924096 6597674795008 545259520 t1m419T11 t1m419T14 (by decide) (by decide) t1m419T11OK t1m419T14OK

private def t1m419T4 : Tree := .split 23 t1m419T5 t1m419T10
private theorem t1m419T4OK : treeOK (staticMotif 1) 419 0 6597137924096 t1m419T4=true :=
  join (staticMotif 1) 419 23 0 6597137924096 6597146312704 8388608 t1m419T5 t1m419T10 (by decide) (by decide) t1m419T5OK t1m419T10OK

private def t1m419T15 : Tree := (.split 14 (.split 15 (.split 36 (.split 37 (.tip (.scoreSmall 6)) (.tip (.noActive 8))) (.tip (.noActive 7))) (.tip (.noActive 8))) (.tip (.noActive 7)))
private theorem t1m419T15OK : treeOK (staticMotif 1) 419 4398046511104 2199091412992 t1m419T15=true := by decide

private def t1m419T3 : Tree := .split 42 t1m419T4 t1m419T15
private theorem t1m419T3OK : treeOK (staticMotif 1) 419 0 2199091412992 t1m419T3=true :=
  join (staticMotif 1) 419 42 0 2199091412992 6597137924096 4398046511104 t1m419T4 t1m419T15 (by decide) (by decide) t1m419T4OK t1m419T15OK

private def t1m419T16 : Tree := (.tip (.noActive 6))
private theorem t1m419T16OK : treeOK (staticMotif 1) 419 67108864 2199024304128 t1m419T16=true := by decide

private def t1m419T2 : Tree := .split 26 t1m419T3 t1m419T16
private theorem t1m419T2OK : treeOK (staticMotif 1) 419 0 2199024304128 t1m419T2=true :=
  join (staticMotif 1) 419 26 0 2199024304128 2199091412992 67108864 t1m419T3 t1m419T16 (by decide) (by decide) t1m419T3OK t1m419T16OK

private def t1m419T17 : Tree := (.tip (.noActive 6))
private theorem t1m419T17OK : treeOK (staticMotif 1) 419 1048576 2199023255552 t1m419T17=true := by decide

private def t1m419T1 : Tree := .split 20 t1m419T2 t1m419T17
private theorem t1m419T1OK : treeOK (staticMotif 1) 419 0 2199023255552 t1m419T1=true :=
  join (staticMotif 1) 419 20 0 2199023255552 2199024304128 1048576 t1m419T2 t1m419T17 (by decide) (by decide) t1m419T2OK t1m419T17OK

private def t1m419T18 : Tree := (.tip (.noActive 6))
private theorem t1m419T18OK : treeOK (staticMotif 1) 419 2199023255552 0 t1m419T18=true := by decide

private def t1m419T0 : Tree := .split 41 t1m419T1 t1m419T18
private theorem t1m419T0OK : treeOK (staticMotif 1) 419 0 0 t1m419T0=true :=
  join (staticMotif 1) 419 41 0 0 2199023255552 2199023255552 t1m419T1 t1m419T18 (by decide) (by decide) t1m419T1OK t1m419T18OK

theorem t1m419_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 1) bits) 419) :
    ∃ D,Cover (withBits (staticMotif 1) bits) D :=
  checked_tree (staticMotif 1) 419 bits H t1m419T0 t1m419T0OK

#print axioms t1m419_cover

private def t1m451T0 : Tree := (.split 38 (.split 42 (.split 23 (.split 19 (.split 25 (.tip (.scoreSmall 5)) (.tip (.noActive 5))) (.tip (.noActive 5))) (.split 29 (.split 19 (.split 25 (.tip (.scoreSmall 5)) (.tip (.noActive 5))) (.tip (.noActive 5))) (.tip (.noActive 9)))) (.split 39 (.split 40 (.split 14 (.split 15 (.split 19 (.split 25 (.tip (.scoreSmall 5)) (.tip (.noActive 5))) (.tip (.noActive 5))) (.tip (.noActive 8))) (.tip (.noActive 7))) (.tip (.noActive 8))) (.tip (.noActive 7)))) (.tip (.noActive 5)))
private theorem t1m451T0OK : treeOK (staticMotif 1) 451 0 0 t1m451T0=true := by decide

theorem t1m451_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 1) bits) 451) :
    ∃ D,Cover (withBits (staticMotif 1) bits) D :=
  checked_tree (staticMotif 1) 451 bits H t1m451T0 t1m451T0OK

#print axioms t1m451_cover

end Graffiti384b.DiversityEleven.CutTen
