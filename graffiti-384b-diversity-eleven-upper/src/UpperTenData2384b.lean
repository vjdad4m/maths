import UpperTenModel384b

namespace Graffiti384b.DiversityEleven.CutTen
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private def t2m181T0 : Tree := (.split 21 (.split 19 (.split 36 (.split 44 (.split 15 (.split 28 (.tip (.scoreSmall 8)) (.split 40 (.tip (.scoreSmall 8)) (.tip (.noActive 8)))) (.split 28 (.split 40 (.tip (.scoreSmall 8)) (.tip (.noActive 8))) (.tip (.noActive 8)))) (.split 15 (.split 16 (.split 28 (.split 29 (.tip (.scoreSmall 5)) (.tip (.noActive 9))) (.tip (.noActive 8))) (.tip (.noActive 9))) (.tip (.noActive 8)))) (.tip (.noActive 5))) (.tip (.noActive 2))) (.tip (.noActive 2)))
private theorem t2m181T0OK : treeOK (staticMotif 2) 181 0 0 t2m181T0=true := by decide

theorem t2m181_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 2) bits) 181) :
    ∃ D,Cover (withBits (staticMotif 2) bits) D :=
  checked_tree (staticMotif 2) 181 bits H t2m181T0 t2m181T0OK

#print axioms t2m181_cover

private def t2m229T5 : Tree := (.split 28 (.tip (.scoreSmall 8)) (.split 16 (.split 29 (.tip (.scoreSmall 9)) (.split 42 (.tip (.scoreSmall 8)) (.split 43 (.tip (.scoreSmall 9)) (.tip (.cover {1,3,4,7}))))) (.split 29 (.split 42 (.tip (.scoreSmall 8)) (.split 43 (.tip (.scoreSmall 9)) (.tip (.cover {1,3,4,7})))) (.tip (.noActive 9)))))
private theorem t2m229T5OK : treeOK (staticMotif 2) 229 0 17592189747200 t2m229T5=true := by decide

private def t2m229T6 : Tree := (.split 28 (.split 16 (.split 29 (.tip (.scoreSmall 9)) (.split 42 (.tip (.scoreSmall 8)) (.split 43 (.tip (.scoreSmall 9)) (.tip (.cover {1,3,4,7}))))) (.split 29 (.split 42 (.tip (.scoreSmall 8)) (.split 23 (.split 22 (.tip (.crossSmall 2)) (.split 43 (.tip (.crossSmall 9)) (.tip (.cover {0,1,4,7})))) (.tip (.cover {1,2,4,7})))) (.tip (.noActive 9)))) (.tip (.noActive 8)))
private theorem t2m229T6OK : treeOK (staticMotif 2) 229 32768 17592189714432 t2m229T6=true := by decide

private def t2m229T4 : Tree := .split 15 t2m229T5 t2m229T6
private theorem t2m229T4OK : treeOK (staticMotif 2) 229 0 17592189714432 t2m229T4=true :=
  join (staticMotif 2) 229 15 0 17592189714432 17592189747200 32768 t2m229T5 t2m229T6 (by decide) (by decide) t2m229T5OK t2m229T6OK

private def t2m229T7 : Tree := (.split 15 (.split 16 (.split 28 (.split 29 (.split 36 (.tip (.scoreSmall 5)) (.split 39 (.tip (.scoreSmall 6)) (.tip (.noActive 7)))) (.tip (.noActive 9))) (.tip (.noActive 8))) (.tip (.noActive 9))) (.tip (.noActive 8)))
private theorem t2m229T7OK : treeOK (staticMotif 2) 229 17592186044416 3670016 t2m229T7=true := by decide

private def t2m229T3 : Tree := .split 44 t2m229T4 t2m229T7
private theorem t2m229T3OK : treeOK (staticMotif 2) 229 0 3670016 t2m229T3=true :=
  join (staticMotif 2) 229 44 0 3670016 17592189714432 17592186044416 t2m229T4 t2m229T7 (by decide) (by decide) t2m229T4OK t2m229T7OK

private def t2m229T8 : Tree := (.tip (.noActive 2))
private theorem t2m229T8OK : treeOK (staticMotif 2) 229 1048576 2621440 t2m229T8=true := by decide

private def t2m229T2 : Tree := .split 20 t2m229T3 t2m229T8
private theorem t2m229T2OK : treeOK (staticMotif 2) 229 0 2621440 t2m229T2=true :=
  join (staticMotif 2) 229 20 0 2621440 3670016 1048576 t2m229T3 t2m229T8 (by decide) (by decide) t2m229T3OK t2m229T8OK

private def t2m229T9 : Tree := (.tip (.noActive 2))
private theorem t2m229T9OK : treeOK (staticMotif 2) 229 524288 2097152 t2m229T9=true := by decide

private def t2m229T1 : Tree := .split 19 t2m229T2 t2m229T9
private theorem t2m229T1OK : treeOK (staticMotif 2) 229 0 2097152 t2m229T1=true :=
  join (staticMotif 2) 229 19 0 2097152 2621440 524288 t2m229T2 t2m229T9 (by decide) (by decide) t2m229T2OK t2m229T9OK

private def t2m229T10 : Tree := (.tip (.noActive 2))
private theorem t2m229T10OK : treeOK (staticMotif 2) 229 2097152 0 t2m229T10=true := by decide

private def t2m229T0 : Tree := .split 21 t2m229T1 t2m229T10
private theorem t2m229T0OK : treeOK (staticMotif 2) 229 0 0 t2m229T0=true :=
  join (staticMotif 2) 229 21 0 0 2097152 2097152 t2m229T1 t2m229T10 (by decide) (by decide) t2m229T1OK t2m229T10OK

theorem t2m229_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 2) bits) 229) :
    ∃ D,Cover (withBits (staticMotif 2) bits) D :=
  checked_tree (staticMotif 2) 229 bits H t2m229T0 t2m229T0OK

#print axioms t2m229_cover

private def t2m403T0 : Tree := (.tip (.noActive 1))
private theorem t2m403T0OK : treeOK (staticMotif 2) 403 0 0 t2m403T0=true := by decide

theorem t2m403_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 2) bits) 403) :
    ∃ D,Cover (withBits (staticMotif 2) bits) D :=
  checked_tree (staticMotif 2) 403 bits H t2m403T0 t2m403T0OK

#print axioms t2m403_cover

private def t2m419T0 : Tree := (.split 41 (.split 20 (.split 26 (.split 42 (.tip (.scoreSmall 6)) (.split 14 (.tip (.scoreSmall 6)) (.tip (.noActive 7)))) (.tip (.noActive 6))) (.tip (.noActive 6))) (.tip (.noActive 6)))
private theorem t2m419T0OK : treeOK (staticMotif 2) 419 0 0 t2m419T0=true := by decide

theorem t2m419_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 2) bits) 419) :
    ∃ D,Cover (withBits (staticMotif 2) bits) D :=
  checked_tree (staticMotif 2) 419 bits H t2m419T0 t2m419T0OK

#print axioms t2m419_cover

end Graffiti384b.DiversityEleven.CutTen
