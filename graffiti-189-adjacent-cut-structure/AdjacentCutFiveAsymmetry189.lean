import AdjacentCutFiveActual189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private d2 mem_positive positive_card from AdjacentCutFiveBound189
open private covered_even from AdjacentCutFiveBound189
open private CutGraph from AdjacentCutFiveActual189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

noncomputable def Exclusive (G : SimpleGraph V) [Fintype V] (a b : V) : Finset V := by
  classical
  exact univ.filter (fun z => z ≠ b ∧ G.Adj a z ∧ ¬ G.Adj b z)

theorem mem_exclusive {z : V} :
    z ∈ Exclusive G a b ↔ z ≠ b ∧ G.Adj a z ∧ ¬ G.Adj b z := by
  classical simp [Exclusive]

theorem order_add_exclusive_le_twenty_two_of_split (S : CrossSaturation.Split G a b)
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ x,(EvenFrom G x).card≤6)
    (rightA : ∃ y∈S.R,G.Adj a y) :
    Fintype.card V + (Exclusive G a b).card ≤ 22 := by
  classical
  obtain ⟨x,xL,ax⟩ := S.leftA
  obtain ⟨y,yR,ay⟩ := rightA
  let A := PositiveEven G a ∪ PositiveEven G b
  let B := PositiveEven G x ∪ PositiveEven G y
  have sub : Exclusive G a b ⊆ A ∩ B := by
    intro z hz
    obtain ⟨zb,az,bz⟩ : z≠b ∧ G.Adj a z ∧ ¬ G.Adj b z := mem_exclusive.mp hz
    have mA : z ∈ A := by
      have e := d2 hc zb.symm bz ab.symm az
      exact mem_union.mpr (.inr (mem_positive.mpr
        ⟨zb, by simp [(mem_filter.mp e).2]⟩))
    refine mem_inter.mpr ⟨mA, ?_⟩
    rcases S.cover z with rfl | rfl | zL | zR
    · exact (az.ne rfl).elim
    · exact (zb rfl).elim
    · have ne : y ≠ z := fun e => disjoint_left.mp S.dis zL (e ▸ yR)
      have d := d2 hc ne (fun e => S.cross z zL y yR e.symm) ay.symm az
      exact mem_union.mpr (.inr (mem_positive.mpr ⟨ne.symm, by simp [(mem_filter.mp d).2]⟩))
    · have ne : x ≠ z := fun e => disjoint_left.mp S.dis (e ▸ xL) zR
      have d := d2 hc ne (S.cross x xL z zR) ax.symm az
      exact mem_union.mpr (.inl (mem_positive.mpr ⟨ne.symm, by simp [(mem_filter.mp d).2]⟩))
  have cov : (univ : Finset V) ⊆ insert a (insert b (A∪B)) := by
    intro z _
    by_cases za : z = a
    · simp [za]
    by_cases zb : z = b
    · simp [zb]
    rcases covered_even S hc ab xL yR (.inl ax) (.inl ay) za zb with h|h|h|h <;>
      simp [A,B,h]
  have size := card_le_card cov
  rw [card_univ] at size
  have insA := card_insert_le a (insert b (A∪B))
  have insB := card_insert_le b (A∪B)
  have cardA := card_union_le (PositiveEven G a) (PositiveEven G b)
  have cardB := card_union_le (PositiveEven G x) (PositiveEven G y)
  change A.card ≤ _ at cardA
  change B.card ≤ _ at cardB
  have ca := positive_card (even a)
  have cb := positive_card (even b)
  have cx := positive_card (even x)
  have cy := positive_card (even y)
  have cnt := card_union_add_card_inter A B
  have m := card_le_card sub
  omega

theorem order_add_exclusive_le_twenty_two_of_actual_adjacent_cut (hc : G.Connected)
    (ab : G.Adj a b) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (cut : 2≤Nat.card (CutGraph (G:=G) a b).ConnectedComponent) :
    Fintype.card V + (Exclusive G a b).card ≤ 22 := by
  obtain ⟨S,ra,_⟩ := actual_split ab.ne conn cut
  exact order_add_exclusive_le_twenty_two_of_split S hc ab even ra

#print axioms order_add_exclusive_le_twenty_two_of_actual_adjacent_cut
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
