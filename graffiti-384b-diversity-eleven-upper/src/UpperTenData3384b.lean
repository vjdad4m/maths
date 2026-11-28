import UpperTenModel384b

namespace Graffiti384b.DiversityEleven.CutTen
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private def t3m121T1 : Tree := (.split 42 (.split 25 (.split 35 (.split 43 (.split 21 (.tip (.scoreSmall 7)) (.split 14 (.tip (.scoreSmall 7)) (.tip (.noActive 7)))) (.split 44 (.split 21 (.split 22 (.tip (.scoreSmall 5)) (.split 23 (.tip (.scoreSmall 5)) (.tip (.noActive 9)))) (.tip (.noActive 7))) (.tip (.noActive 9)))) (.tip (.noActive 5))) (.tip (.noActive 3))) (.split 43 (.split 44 (.split 21 (.split 22 (.split 25 (.split 23 (.tip (.scoreSmall 9)) (.split 35 (.tip (.scoreSmall 5)) (.tip (.noActive 5)))) (.tip (.noActive 3))) (.tip (.noActive 8))) (.tip (.noActive 7))) (.tip (.noActive 8))) (.tip (.noActive 7))))
private theorem t3m121T1OK : treeOK (staticMotif 3) 121 0 67108864 t3m121T1=true := by decide

private def t3m121T2 : Tree := (.tip (.noActive 3))
private theorem t3m121T2OK : treeOK (staticMotif 3) 121 67108864 0 t3m121T2=true := by decide

private def t3m121T0 : Tree := .split 26 t3m121T1 t3m121T2
private theorem t3m121T0OK : treeOK (staticMotif 3) 121 0 0 t3m121T0=true :=
  join (staticMotif 3) 121 26 0 0 67108864 67108864 t3m121T1 t3m121T2 (by decide) (by decide) t3m121T1OK t3m121T2OK

theorem t3m121_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 3) bits) 121) :
    ∃ D,Cover (withBits (staticMotif 3) bits) D :=
  checked_tree (staticMotif 3) 121 bits H t3m121T0 t3m121T0OK

#print axioms t3m121_cover

private def t3m211T0 : Tree := (.tip (.noActive 1))
private theorem t3m211T0OK : treeOK (staticMotif 3) 211 0 0 t3m211T0=true := by decide

theorem t3m211_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 3) bits) 211) :
    ∃ D,Cover (withBits (staticMotif 3) bits) D :=
  checked_tree (staticMotif 3) 211 bits H t3m211T0 t3m211T0OK

#print axioms t3m211_cover

private def t3m213T0 : Tree := (.tip (.noActive 2))
private theorem t3m213T0OK : treeOK (staticMotif 3) 213 0 0 t3m213T0=true := by decide

theorem t3m213_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 3) bits) 213) :
    ∃ D,Cover (withBits (staticMotif 3) bits) D :=
  checked_tree (staticMotif 3) 213 bits H t3m213T0 t3m213T0OK

#print axioms t3m213_cover

private def t3m227T1 : Tree := (.split 41 (.tip (.crossSmall 6)) (.split 42 (.tip (.crossSmall 8)) (.split 20 (.tip (.crossSmall 6)) (.split 26 (.tip (.crossSmall 6)) (.split 15 (.tip (.crossSmall 8)) (.split 37 (.tip (.crossSmall 8)) (.split 43 (.split 21 (.tip (.crossSmall 7)) (.tip (.cover {1,2,8,9}))) (.tip (.cover {1,2,8,9})))))))))
private theorem t3m227T1OK : treeOK (staticMotif 3) 227 0 1099511627776 t3m227T1=true := by decide

private def t3m227T3 : Tree := (.split 43 (.tip (.crossSmall 9)) (.split 20 (.tip (.crossSmall 6)) (.split 26 (.tip (.crossSmall 6)) (.split 16 (.tip (.crossSmall 9)) (.split 37 (.split 42 (.tip (.crossSmall 8)) (.split 15 (.tip (.crossSmall 8)) (.split 38 (.tip (.crossSmall 9)) (.tip (.cover {1,2,8,9}))))) (.tip (.cover {1,2,7,8})))))))
private theorem t3m227T3OK : treeOK (staticMotif 3) 227 1099511627776 2199023255552 t3m227T3=true := by decide

private def t3m227T5 : Tree := (.split 43 (.tip (.crossSmall 7)) (.split 21 (.tip (.crossSmall 7)) (.split 27 (.tip (.crossSmall 7)) (.split 15 (.tip (.crossSmall 8)) (.split 37 (.tip (.crossSmall 8)) (.tip (.cover {1,2,8,9})))))))
private theorem t3m227T5OK : treeOK (staticMotif 3) 227 3298534883328 4398046511104 t3m227T5=true := by decide

private def t3m227T7 : Tree := (.split 21 (.tip (.crossSmall 7)) (.split 27 (.tip (.crossSmall 7)) (.split 16 (.tip (.crossSmall 9)) (.split 37 (.split 15 (.tip (.crossSmall 8)) (.split 38 (.tip (.crossSmall 9)) (.tip (.cover {1,2,8,9})))) (.tip (.cover {1,2,6,8}))))))
private theorem t3m227T7OK : treeOK (staticMotif 3) 227 7696581394432 8796093022208 t3m227T7=true := by decide

private def t3m227T10 : Tree := (.tip (.crossSmall 6))
private theorem t3m227T10OK : treeOK (staticMotif 3) 227 16492674416640 68157440 t3m227T10=true := by decide

private def t3m227T11 : Tree := (.split 37 (.split 15 (.tip (.crossSmall 8)) (.split 38 (.split 16 (.tip (.crossSmall 9)) (.split 25 (.tip (.crossSmall 5)) (.split 39 (.split 21 (.split 27 (.tip (.crossSmall 7)) (.split 44 (.split 22 (.split 23 (.split 28 (.tip (.degreeSmall 8)) (.tip (.cover {1,3,5,9}))) (.tip (.cover {1,2,3,8}))) (.tip (.cover {1,2,3,9}))) (.tip (.cover {1,3,5,8})))) (.split 27 (.split 44 (.split 22 (.split 23 (.split 28 (.tip (.degreeSmall 8)) (.tip (.cover {1,2,3,9}))) (.tip (.cover {1,2,3,8}))) (.tip (.cover {1,2,3,9}))) (.tip (.cover {1,2,3,8}))) (.tip (.cover {1,2,3,6})))) (.tip (.cover {1,3,5,7}))))) (.tip (.cover {1,2,8,9})))) (.tip (.cover {1,2,8,9})))
private theorem t3m227T11OK : treeOK (staticMotif 3) 227 16492741525504 1048576 t3m227T11=true := by decide

private def t3m227T9 : Tree := .split 26 t3m227T10 t3m227T11
private theorem t3m227T9OK : treeOK (staticMotif 3) 227 16492674416640 1048576 t3m227T9=true :=
  join (staticMotif 3) 227 26 16492674416640 1048576 68157440 16492741525504 t3m227T10 t3m227T11 (by decide) (by decide) t3m227T10OK t3m227T11OK

private def t3m227T12 : Tree := (.split 37 (.split 15 (.tip (.crossSmall 8)) (.split 38 (.split 16 (.tip (.crossSmall 9)) (.split 25 (.tip (.crossSmall 5)) (.split 26 (.split 39 (.split 21 (.split 27 (.tip (.crossSmall 7)) (.split 44 (.split 22 (.split 23 (.split 28 (.tip (.degreeSmall 8)) (.tip (.cover {1,2,3,9}))) (.tip (.cover {1,2,3,8}))) (.tip (.cover {1,2,3,9}))) (.tip (.cover {1,2,3,8})))) (.split 27 (.split 44 (.split 22 (.tip (.scoreSmall 8)) (.tip (.cover {1,2,4,9}))) (.tip (.cover {1,2,4,8}))) (.tip (.cover {1,2,3,6})))) (.tip (.cover {1,2,4,7}))) (.tip (.cover {1,2,3,7}))))) (.tip (.cover {1,2,7,9})))) (.tip (.cover {1,2,8,9})))
private theorem t3m227T12OK : treeOK (staticMotif 3) 227 16492675465216 0 t3m227T12=true := by decide

private def t3m227T8 : Tree := .split 20 t3m227T9 t3m227T12
private theorem t3m227T8OK : treeOK (staticMotif 3) 227 16492674416640 0 t3m227T8=true :=
  join (staticMotif 3) 227 20 16492674416640 0 1048576 16492675465216 t3m227T9 t3m227T12 (by decide) (by decide) t3m227T9OK t3m227T12OK

private def t3m227T6 : Tree := .split 43 t3m227T7 t3m227T8
private theorem t3m227T6OK : treeOK (staticMotif 3) 227 7696581394432 0 t3m227T6=true :=
  join (staticMotif 3) 227 43 7696581394432 0 8796093022208 16492674416640 t3m227T7 t3m227T8 (by decide) (by decide) t3m227T7OK t3m227T8OK

private def t3m227T4 : Tree := .split 42 t3m227T5 t3m227T6
private theorem t3m227T4OK : treeOK (staticMotif 3) 227 3298534883328 0 t3m227T4=true :=
  join (staticMotif 3) 227 42 3298534883328 0 4398046511104 7696581394432 t3m227T5 t3m227T6 (by decide) (by decide) t3m227T5OK t3m227T6OK

private def t3m227T2 : Tree := .split 41 t3m227T3 t3m227T4
private theorem t3m227T2OK : treeOK (staticMotif 3) 227 1099511627776 0 t3m227T2=true :=
  join (staticMotif 3) 227 41 1099511627776 0 2199023255552 3298534883328 t3m227T3 t3m227T4 (by decide) (by decide) t3m227T3OK t3m227T4OK

private def t3m227T0 : Tree := .split 40 t3m227T1 t3m227T2
private theorem t3m227T0OK : treeOK (staticMotif 3) 227 0 0 t3m227T0=true :=
  join (staticMotif 3) 227 40 0 0 1099511627776 1099511627776 t3m227T1 t3m227T2 (by decide) (by decide) t3m227T1OK t3m227T2OK

theorem t3m227_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 3) bits) 227) :
    ∃ D,Cover (withBits (staticMotif 3) bits) D :=
  checked_tree (staticMotif 3) 227 bits H t3m227T0 t3m227T0OK

#print axioms t3m227_cover

private def t3m229T1 : Tree := (.split 41 (.tip (.crossSmall 6)) (.split 42 (.tip (.crossSmall 8)) (.split 22 (.tip (.crossSmall 8)) (.split 26 (.tip (.crossSmall 6)) (.split 13 (.tip (.crossSmall 6)) (.split 37 (.tip (.crossSmall 8)) (.split 43 (.split 23 (.tip (.crossSmall 9)) (.split 27 (.tip (.crossSmall 7)) (.split 14 (.tip (.crossSmall 7)) (.tip (.cover {1,2,6,8}))))) (.tip (.cover {1,2,8,9})))))))))
private theorem t3m229T1OK : treeOK (staticMotif 3) 229 0 1099511627776 t3m229T1=true := by decide

private def t3m229T3 : Tree := (.split 43 (.tip (.crossSmall 9)) (.split 23 (.tip (.crossSmall 9)) (.split 26 (.tip (.crossSmall 6)) (.split 13 (.tip (.crossSmall 6)) (.split 37 (.split 42 (.tip (.crossSmall 8)) (.split 22 (.tip (.crossSmall 8)) (.split 38 (.tip (.crossSmall 5)) (.tip (.cover {1,2,8,9}))))) (.tip (.cover {1,2,7,8})))))))
private theorem t3m229T3OK : treeOK (staticMotif 3) 229 1099511627776 2199023255552 t3m229T3=true := by decide

private def t3m229T4 : Tree := (.split 42 (.split 43 (.tip (.crossSmall 7)) (.split 22 (.tip (.crossSmall 8)) (.split 27 (.tip (.crossSmall 7)) (.split 14 (.tip (.crossSmall 7)) (.split 37 (.tip (.crossSmall 8)) (.tip (.cover {1,2,8,9}))))))) (.split 43 (.split 23 (.tip (.crossSmall 9)) (.split 27 (.tip (.crossSmall 7)) (.split 14 (.tip (.crossSmall 7)) (.split 37 (.split 22 (.tip (.crossSmall 8)) (.split 38 (.tip (.crossSmall 5)) (.tip (.cover {1,2,8,9})))) (.tip (.cover {1,2,6,8})))))) (.split 22 (.split 37 (.tip (.crossSmall 8)) (.tip (.cover {1,2,8,9}))) (.split 37 (.split 38 (.tip (.crossSmall 5)) (.tip (.cover {1,2,8,9}))) (.tip (.cover {1,2,8,9}))))))
private theorem t3m229T4OK : treeOK (staticMotif 3) 229 3298534883328 0 t3m229T4=true := by decide

private def t3m229T2 : Tree := .split 41 t3m229T3 t3m229T4
private theorem t3m229T2OK : treeOK (staticMotif 3) 229 1099511627776 0 t3m229T2=true :=
  join (staticMotif 3) 229 41 1099511627776 0 2199023255552 3298534883328 t3m229T3 t3m229T4 (by decide) (by decide) t3m229T3OK t3m229T4OK

private def t3m229T0 : Tree := .split 40 t3m229T1 t3m229T2
private theorem t3m229T0OK : treeOK (staticMotif 3) 229 0 0 t3m229T0=true :=
  join (staticMotif 3) 229 40 0 0 1099511627776 1099511627776 t3m229T1 t3m229T2 (by decide) (by decide) t3m229T1OK t3m229T2OK

theorem t3m229_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 3) bits) 229) :
    ∃ D,Cover (withBits (staticMotif 3) bits) D :=
  checked_tree (staticMotif 3) 229 bits H t3m229T0 t3m229T0OK

#print axioms t3m229_cover

end Graffiti384b.DiversityEleven.CutTen
