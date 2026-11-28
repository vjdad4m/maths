import SixPack0
import SixPack1
import SixPack2
import SixPack3
import SixPack4
import SixPack5
import SixPack6
import SixTransfer
import SixLayout
namespace Graffiti384b.SixFront.Model
open Finset SimpleGraph Four29

private def required : Fin 7 → ℕ := ![33,97,1121,33889,2131041,270566497,68990043233]
private def absent : Fin 7 → ℕ := ![68990043200,68990043136,68990042112,68990009344,68987912192,68719476736,0]

set_option maxHeartbeats 0 in
/-- Positions occupied by the two fixed ear-mate edges and the sorted contacts. -/
private theorem layout_bits : ∀k:Fin 7,∀i:Fin 45,
    ((required k).testBit i.val=true → i.val=position 0 1 ∨ i.val=position 2 3 ∨
       ∃j:Fin 6,j.val<k.val ∧ i.val=position 0 (atContact j)) ∧
    ((absent k).testBit i.val=true → ∃j:Fin 6,k.val≤j.val ∧ i.val=position 0 (atContact j)) := by decide

theorem finite_six : Claim := by
  intro k a mate1 mate2 sorted rich
  have room : required k<2^45 ∧ absent k<2^45 :=
    (show ∀j:Fin 7,required j<2^45 ∧ absent j<2^45 by decide) k
  have lb : Below (on (required k)) a := by
    intro i bit
    by_cases small : i<45
    · rcases (layout_bits k ⟨i,small⟩).1 bit with eq|eq|⟨j,jk,eq⟩
      · change i=position 0 1 at eq; rwa [eq]
      · change i=position 2 3 at eq; rwa [eq]
      · change i=position 0 (atContact j) at eq; rw [eq]; exact (sorted j).mpr jk
    · have far := Nat.testBit_lt_two_pow (room.1.trans_le (Nat.pow_le_pow_right (by decide) (by omega : 45 ≤ i)))
      simp [on,far] at bit
  have ub : Below a (allowed (absent k)) := by
    intro i ai
    by_cases sm : i<45
    · by_cases bit : (absent k).testBit i=true
      · obtain ⟨j,jk,eq⟩ := (layout_bits k ⟨i,sm⟩).2 bit
        change i=position 0 (atContact j) at eq
        rw [eq] at ai
        exact (not_lt_of_ge jk ((sorted j).mp ai)).elim
      · simp [allowed,Bool.eq_false_iff.mpr bit]
    · have far := Nat.testBit_lt_two_pow (room.2.trans_le (Nat.pow_le_pow_right (by decide) (by omega : 45 ≤ i)))
      simp [allowed,far]
  fin_cases k
  · exact check_sound a rich case0_root _ _ lb ub case0_root_ok
  · exact check_sound a rich case1_root _ _ lb ub case1_root_ok
  · exact check_sound a rich case2_root _ _ lb ub case2_root_ok
  · exact check_sound a rich case3_root _ _ lb ub case3_root_ok
  · exact check_sound a rich case4_root _ _ lb ub case4_root_ok
  · exact check_sound a rich case5_root _ _ lb ub case5_root_ok
  · exact check_sound a rich case6_root _ _ lb ub case6_root_ok

end Graffiti384b.SixFront.Model
namespace Graffiti384b.SixFront
open Finset SimpleGraph Four29
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Exact six-contact closure, at every graph order. The two degree-two
vertices are arbitrary. Four distinct high anchors follow from a failure. -/
theorem six_contacts (t : (types G).card=29) (q : (nonleaves G).card=29) (h : (high G).card=27)
    {e f : V} (de : G.degree e=2) (df : G.degree f=2) (ef : e≠f)
    (six : (triangleContacts G e f).card=6) : gamma G≤bound G := by
  apply Nat.le_of_not_gt; intro bad
  obtain ⟨frame⟩ := Model.failure_layout G t q h bad de df ef six
  exact (not_lt_of_ge (Model.from_layout G Model.finite_six t q h frame)) bad

theorem remaining_contacts (t : (types G).card=29) (q : (nonleaves G).card=29) (h : (high G).card=27)
    (bad : bound G<gamma G) {e f : V} (de : G.degree e=2) (df : G.degree f=2) (ef : e≠f) :
    7≤(triangleContacts G e f).card ∧ (triangleContacts G e f).card≤14 := by
  obtain ⟨_,lo,tm,hi,_⟩ := five_contact_residual G t h q bad de df ef
  refine ⟨lt_of_le_of_ne lo ?_,tm.trans hi⟩
  intro eq
  exact (not_lt_of_ge (six_contacts G t q h de df ef eq.symm)) bad
end Graffiti384b.SixFront
#print axioms Graffiti384b.SixFront.Model.finite_six
#print axioms Graffiti384b.SixFront.six_contacts
#print axioms Graffiti384b.SixFront.remaining_contacts

