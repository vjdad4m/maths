import SixSingletonQ1Sparse0Actual189
import SixSingletonQ1Sparse1Actual189
import SixSingletonQ1Sparse2Actual189
import SixSingletonQ1Dense0Actual189
import SixSingletonQ1Dense1Actual189
import SixSingletonQ1Dense2Actual189
import SixSingletonQ1Isolated0Actual189
import SixSingletonQ1Isolated1Actual189
import SixSingletonQ1Isolated2Actual189
import SixSingletonQ1ExceptionActual189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair Graffiti189Ore PortCertificates
open private Shore from AdjacentCutFiveActual189
open private Cmp DeletionConnected aPorts bPorts from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark Common strictA strictB from SixSingletonGeometry189
open private nearLeft nearRight nearBal from SixSingletonFiveGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b s z : V} {D : Cmp G a b}
set_option linter.unusedSectionVars false
set_option maxHeartbeats 14000000

private theorem q1_row0 (F : SixVisibleData G D s) (n : Fintype.card V=16) (ab : G.Adj a b)
    (v6 : (Vis D).card=6) (bal : nearBal D={z})
    (ea : (EA D).card=2) (eb : (EB D).card=2) (la : (strictA D).card=3) (rb : (strictB D).card=3) :
    Traceable G := by
  classical
  obtain ⟨P⟩ := q1_port_board_two F v6 ea eb
  let h := (inside G (Dark D) z).card
  by_cases zero : h=0
  · exact Q1Isolated0Actual.run F P n ab bal ea eb la rb zero v6
  by_cases dense : 4≤h
  · exact Q1Dense0Actual.run F P n ab bal ea eb la rb dense
  obtain ⟨w,wm⟩ := card_pos.mp (show 0<(inside G (Dark D) z).card from Nat.pos_of_ne_zero zero)
  obtain ⟨wd,zw⟩ := mem_filter.mp wm
  have low : (inside G (Dark D) z).card≤3 := Nat.le_of_lt_succ (Nat.lt_of_not_ge dense)
  exact Q1Sparse0Actual.run F P n ab bal ea eb la rb low (mem_erase.mpr ⟨zw.ne.symm,wd⟩) zw.symm

private theorem q1_row1 (F : SixVisibleData G D s) (n : Fintype.card V=16) (ab : G.Adj a b)
    (v6 : (Vis D).card=6) (bal : nearBal D={z})
    (ea : (EA D).card=1) (eb : (EB D).card=2) (la : (strictA D).card=2) (rb : (strictB D).card=4) :
    Traceable G := by
  classical
  obtain ⟨P⟩ := q1_port_board_one F v6 ea eb
  let f (i : Fin 6) := P.label (widenQ1 (by decide : 6≤9) i)
  by_cases bad : Q1Sparse1.Bad (Q1Sparse1Actual.bits (G:=G) f z)
  · exact q1_exception_traceable F P n bal (by omega) (by omega) v6 la rb bad
  let h := (inside G (Dark D) z).card
  by_cases zero : h=0
  · exact Q1Isolated1Actual.run F P n ab bal ea eb la rb zero v6
  by_cases dense : 4≤h
  · refine Q1Dense1Actual.run F P n ab bal ea eb la rb dense ?_
    intro e
    apply bad
    simpa [Q1Sparse1.Bad,Q1Dense1.Bad,Q1Sparse1Actual.bits,Q1Dense1Actual.bits,f] using e
  obtain ⟨w,wm⟩ := card_pos.mp (show 0<(inside G (Dark D) z).card from Nat.pos_of_ne_zero zero)
  obtain ⟨wd,zw⟩ := mem_filter.mp wm
  have low : (inside G (Dark D) z).card≤3 := Nat.le_of_lt_succ (Nat.lt_of_not_ge dense)
  exact Q1Sparse1Actual.run F P n ab bal ea eb la rb low (mem_erase.mpr ⟨zw.ne.symm,wd⟩) zw.symm bad

private theorem q1_row2 (F : SixVisibleData G D s) (n : Fintype.card V=16) (ab : G.Adj a b)
    (v6 : (Vis D).card=6) (bal : nearBal D={z})
    (ea : (EA D).card=1) (eb : (EB D).card=2) (la : (strictA D).card=3) (rb : (strictB D).card=3) :
    Traceable G := by
  classical
  obtain ⟨P⟩ := q1_port_board_one F v6 ea eb
  let h := (inside G (Dark D) z).card
  by_cases zero : h=0
  · exact Q1Isolated2Actual.run F P n ab bal ea eb la rb zero v6
  by_cases dense : 4≤h
  · exact Q1Dense2Actual.run F P n ab bal ea eb la rb dense
  obtain ⟨w,wm⟩ := card_pos.mp (show 0<(inside G (Dark D) z).card from Nat.pos_of_ne_zero zero)
  obtain ⟨wd,zw⟩ := mem_filter.mp wm
  have low : (inside G (Dark D) z).card≤3 := Nat.le_of_lt_succ (Nat.lt_of_not_ge dense)
  exact Q1Sparse2Actual.run F P n ab bal ea eb la rb low (mem_erase.mpr ⟨zw.ne.symm,wd⟩) zw.symm


theorem traceable_at_adjacent_singleton_thirteen_six_visible_one_balance_right_two
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ z,(EvenFrom G z).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v) (n : Fintype.card V=16)
    {S D : Cmp G a b} (sd : S≠D)
    (cov : ∀ {z : V},z≠a → z≠b → z∈Shore S ∨ z∈Shore D)
    (one : (Shore S).card=1) (d13 : (Shore D).card=13) (v6 : (Vis D).card=6)
    (b2 : (EB D).card=2) (q1 : (nearBal D).card=1) : Traceable G := by
  classical
  obtain ⟨s,F⟩ := isolate_six_visible_geometry hc ab even conn degree sd cov one d13 v6
  obtain ⟨z,zEq⟩ := card_eq_one.mp q1
  have r := adjacent_six_positive_profile_counts hc ab even conn degree sd cov one d13 v6 b2 (by omega)
  change ((EA D).card=2 ∧ (nearBal D).card=1 ∧ (nearLeft D).card=3 ∧ (nearRight D).card=3) ∨
    ((EA D).card=1 ∧ (nearBal D).card=1 ∧
      (((nearLeft D).card=2 ∧ (nearRight D).card=4) ∨ ((nearLeft D).card=3 ∧ (nearRight D).card=3))) ∨
    ((EA D).card=1 ∧ (nearBal D).card=2 ∧ (nearLeft D).card=2 ∧ (nearRight D).card=3) at r
  rw [F.nearA,F.nearB] at r
  rcases r with ⟨ea,_,la,rb⟩|⟨ea,_,⟨la,rb⟩|⟨la,rb⟩⟩|⟨_,q,_,_⟩
  · exact q1_row0 F n ab v6 zEq ea b2 la rb
  · exact q1_row1 F n ab v6 zEq ea b2 la rb
  · exact q1_row2 F n ab v6 zEq ea b2 la rb
  omega

#print axioms traceable_at_adjacent_singleton_thirteen_six_visible_one_balance_right_two
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
