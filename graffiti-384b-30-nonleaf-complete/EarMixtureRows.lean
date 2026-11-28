import HighBasics28
namespace Graffiti384b.EarMix
open Finset HighSquare28

def exterior (d a b c k l : ℕ) :=
  2*(bill 21 k d a+bill 21 k d b+bill 21 k d c)+
  5*(bill 21 l d (b+c)+bill 21 l d (c+a)+bill 21 l d (a+b))
def allSelected := 3*(2*(20:ℕ).choose 8+5*(20:ℕ).choose 7)
def oneBill (k d h : ℕ) := if h=0 then (21-d).choose k else 0
def side (d b c : ℕ) := 2*(oneBill 9 d b+oneBill 9 d c)+5*oneBill 8 d (b+c)
def row (i : ℕ) : ℕ := [1823250,1256970,1256970,1256970,802230,802230,802230,802230,544830,544830,544830,544830,544830,341770,341770,341770,341770,341770,341770,227227,227227,198055,198055,198055,198055,198055,198055][i]?.getD 0
private def extOK (r : Fin 27) : Prop := ∀ d : Fin 21,∀ a b c : Fin 3,
      let m := d.val+(a.val+b.val+c.val)
      r.val+2≤m.choose 2 →
      (r.val+2<m.choose 2 → exterior d a b c 9 8≤row r) ∧
      exterior d a b c 9 8+min allSelected (exterior d a b c 8 7)≤row r+allSelected
private def anchorOK (r : Fin 27) : Prop := ∀d : Fin 22,∀a : Fin 2,∀b c : Fin 3,
      r.val+2≤(d.val+(a.val+b.val+c.val)).choose 2+1 → side d b c+175032≤row r

set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

private def valid (r : Fin 27) : Prop := extOK r ∧ anchorOK r
-- Separate kernel reductions bound the memory used in a full replay.
private theorem rank00 : valid 0 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank01 : valid 1 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank02 : valid 2 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank03 : valid 3 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank04 : valid 4 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank05 : valid 5 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank06 : valid 6 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank07 : valid 7 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank08 : valid 8 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank09 : valid 9 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank10 : valid 10 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank11 : valid 11 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank12 : valid 12 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank13 : valid 13 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank14 : valid 14 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank15 : valid 15 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank16 : valid 16 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank17 : valid 17 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank18 : valid 18 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank19 : valid 19 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank20 : valid 20 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank21 : valid 21 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank22 : valid 22 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank23 : valid 23 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank24 : valid 24 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank25 : valid 25 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide
private theorem rank26 : valid 26 := by
  unfold valid extOK anchorOK exterior side oneBill row allSelected bill FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide

private theorem all_valid (r : Fin 27) : valid r := by
  fin_cases r
  · exact rank00
  · exact rank01
  · exact rank02
  · exact rank03
  · exact rank04
  · exact rank05
  · exact rank06
  · exact rank07
  · exact rank08
  · exact rank09
  · exact rank10
  · exact rank11
  · exact rank12
  · exact rank13
  · exact rank14
  · exact rank15
  · exact rank16
  · exact rank17
  · exact rank18
  · exact rank19
  · exact rank20
  · exact rank21
  · exact rank22
  · exact rank23
  · exact rank24
  · exact rank25
  · exact rank26

theorem rows :
    (∀r : Fin 27,∀ d : Fin 21,∀ a b c : Fin 3,
      let m := d.val+(a.val+b.val+c.val)
      r.val+2≤m.choose 2 →
      (r.val+2<m.choose 2 → exterior d a b c 9 8≤row r) ∧
      exterior d a b c 9 8+min allSelected (exterior d a b c 8 7)≤row r+allSelected) ∧
    (∀r : Fin 27,∀d : Fin 22,∀a : Fin 2,∀b c : Fin 3,
      r.val+2≤(d.val+(a.val+b.val+c.val)).choose 2+1 → side d b c+175032≤row r) ∧
    (∑ i∈range 27,row i)=15220634 :=
  ⟨fun r => (all_valid r).1,fun r => (all_valid r).2,by decide⟩
end Graffiti384b.EarMix
#print axioms Graffiti384b.EarMix.rows
