import UpperTenModel384b

namespace Graffiti384b.DiversityEleven.CutTen
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private def t0m307T0 : Tree := (.split 15 (.split 12 (.split 37 (.split 23 (.split 29 (.split 43 (.tip (.scoreSmall 9)) (.split 41 (.tip (.scoreSmall 9)) (.tip (.noActive 9)))) (.split 43 (.split 41 (.tip (.scoreSmall 9)) (.tip (.noActive 9))) (.tip (.noActive 9)))) (.split 29 (.split 43 (.split 41 (.tip (.scoreSmall 9)) (.tip (.noActive 9))) (.tip (.noActive 9))) (.tip (.noActive 9)))) (.tip (.noActive 5))) (.tip (.noActive 1))) (.tip (.noActive 1)))
private theorem t0m307T0OK : treeOK (staticMotif 0) 307 0 0 t0m307T0=true := by decide

theorem t0m307_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 0) bits) 307) :
    ∃ D,Cover (withBits (staticMotif 0) bits) D :=
  checked_tree (staticMotif 0) 307 bits H t0m307T0 t0m307T0OK

#print axioms t0m307_cover

private def t0m355T0 : Tree := (.split 15 (.split 43 (.split 21 (.split 27 (.split 12 (.split 13 (.split 37 (.tip (.scoreSmall 7)) (.split 40 (.tip (.scoreSmall 7)) (.tip (.noActive 8)))) (.tip (.noActive 1))) (.tip (.noActive 1))) (.tip (.noActive 7))) (.tip (.noActive 7))) (.tip (.noActive 7))) (.tip (.noActive 1)))
private theorem t0m355T0OK : treeOK (staticMotif 0) 355 0 0 t0m355T0=true := by decide

theorem t0m355_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 0) bits) 355) :
    ∃ D,Cover (withBits (staticMotif 0) bits) D :=
  checked_tree (staticMotif 0) 355 bits H t0m355T0 t0m355T0OK

#print axioms t0m355_cover

private def t0m403T0 : Tree := (.split 14 (.split 15 (.split 42 (.split 23 (.split 29 (.split 38 (.tip (.scoreSmall 9)) (.split 41 (.tip (.scoreSmall 9)) (.tip (.noActive 9)))) (.split 38 (.split 41 (.tip (.scoreSmall 9)) (.tip (.noActive 9))) (.tip (.noActive 9)))) (.split 29 (.split 38 (.split 41 (.tip (.scoreSmall 9)) (.tip (.noActive 9))) (.tip (.noActive 9))) (.tip (.noActive 9)))) (.tip (.noActive 7))) (.tip (.noActive 1))) (.tip (.noActive 1)))
private theorem t0m403T0OK : treeOK (staticMotif 0) 403 0 0 t0m403T0=true := by decide

theorem t0m403_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 0) bits) 403) :
    ∃ D,Cover (withBits (staticMotif 0) bits) D :=
  checked_tree (staticMotif 0) 403 bits H t0m403T0 t0m403T0OK

#print axioms t0m403_cover

private def t0m419T0 : Tree := (.split 15 (.split 14 (.split 41 (.split 12 (.split 20 (.split 26 (.tip (.scoreSmall 6)) (.tip (.noActive 6))) (.tip (.noActive 6))) (.tip (.noActive 1))) (.tip (.noActive 6))) (.tip (.noActive 1))) (.tip (.noActive 1)))
private theorem t0m419T0OK : treeOK (staticMotif 0) 419 0 0 t0m419T0=true := by decide

theorem t0m419_cover (bits : Nat→Bool) (H : Admissible (withBits (staticMotif 0) bits) 419) :
    ∃ D,Cover (withBits (staticMotif 0) bits) D :=
  checked_tree (staticMotif 0) 419 bits H t0m419T0 t0m419T0OK

#print axioms t0m419_cover

end Graffiti384b.DiversityEleven.CutTen
