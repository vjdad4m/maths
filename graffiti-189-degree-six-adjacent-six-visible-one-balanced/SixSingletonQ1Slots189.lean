import SixSingletonPositiveGeometry189
import SixSingletonPortScore189
import SixSingletonDarkOre189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair
open private Cmp from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark Common strictA strictB from SixSingletonGeometry189
open private nearBal from SixSingletonFiveGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
open private erase_internal_deg from SixSingletonDarkOre189
open PortCertificates (marks)
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b s z : V} {D : Cmp G a b}
set_option linter.unusedSectionVars false

theorem six_q1_left_slots (F : SixVisibleData G D s) (bal : nearBal D = {z})
    {x : V} (hx : x∈EA D) :
    5-(strictA D).card ≤ (inside G (Vis D) x).card + marks (decide (G.Adj x z)) := by
  have h := card_le_card (F.aBound x hx)
  have k : (inside G (nearBal D) x).card = marks (decide (G.Adj x z)) := by
    rw [bal]
    by_cases e : G.Adj x z <;> simp [inside,Finset.filter_singleton,e,marks]
  have h' := card_insert_le a (inside G (Vis D) x ∪ inside G (strictA D) x ∪ inside G (nearBal D) x)
  have i := card_union_le (inside G (Vis D) x ∪ inside G (strictA D) x) (inside G (nearBal D) x)
  have j := card_union_le (inside G (Vis D) x) (inside G (strictA D) x)
  have u := card_le_card (filter_subset (G.Adj x) (strictA D))
  have pos := F.highEA x hx
  rw [←card_neighborFinset_eq_degree] at pos
  change (inside G (strictA D) x).card ≤ (strictA D).card at u
  omega

theorem six_q1_right_slots (F : SixVisibleData G D s) (bal : nearBal D = {z})
    {x : V} (hx : x∈EB D) :
    5-(strictB D).card ≤ (inside G (Vis D) x).card + marks (decide (G.Adj x z)) := by
  have h := card_le_card (F.bBound x hx)
  have k : (inside G (nearBal D) x).card = marks (decide (G.Adj x z)) := by
    rw [bal]
    by_cases e : G.Adj x z <;> simp [inside,Finset.filter_singleton,e,marks]
  have h' := card_insert_le b (inside G (Vis D) x ∪ inside G (strictB D) x ∪ inside G (nearBal D) x)
  have i := card_union_le (inside G (Vis D) x ∪ inside G (strictB D) x) (inside G (nearBal D) x)
  have j := card_union_le (inside G (Vis D) x) (inside G (strictB D) x)
  have u := card_le_card (filter_subset (G.Adj x) (strictB D))
  have pos := F.highEB x hx
  rw [←card_neighborFinset_eq_degree] at pos
  change (inside G (strictB D) x).card ≤ (strictB D).card at u
  omega

theorem six_q1_common_slots (F : SixVisibleData G D s) (bal : nearBal D = {z})
    {x : V} (hx : x∈Common D) :
    4 ≤ (inside G (Vis D) x).card + marks (decide (G.Adj x z)) := by
  have h := card_le_card (F.commonBound x hx)
  have k : (inside G (nearBal D) x).card = marks (decide (G.Adj x z)) := by
    rw [bal]
    by_cases e : G.Adj x z <;> simp [inside,Finset.filter_singleton,e,marks]
  have h' := card_insert_le a (insert b (inside G (Vis D) x ∪ inside G (nearBal D) x))
  have i := card_insert_le b (inside G (Vis D) x ∪ inside G (nearBal D) x)
  have j := card_union_le (inside G (Vis D) x) (inside G (nearBal D) x)
  have pos := F.highCommon x hx
  rw [←card_neighborFinset_eq_degree] at pos
  omega

theorem six_q1_balance_port_slots (F : SixVisibleData G D s) (bal : nearBal D = {z}) :
    6-(inside G (Dark D) z).card ≤ (inside G (Vis D) z).card := by
  have zm : z∈Dark D := by rw [←F.darkPart,bal]; simp
  have h := card_le_card (F.darkBound z zm)
  have i := card_union_le (inside G (Dark D) z) (inside G (Vis D) z)
  have pos := F.highDark z zm
  rw [←card_neighborFinset_eq_degree] at pos
  omega

theorem six_q1_core_bounds (F : SixVisibleData G D s) (bal : nearBal D = {z})
    (ea : (EA D).card≤2) (eb : (EB D).card≤2) :
    (Dark D |>.erase z).card = 6 ∧
    (∀ x∈(Dark D).erase z,3 ≤ (inside G ((Dark D).erase z) x).card) := by
  have zm : z∈Dark D := by rw [←F.darkPart,bal]; simp
  refine ⟨by rw [card_erase_of_mem zm,F.dark7],?_⟩
  intro x xm
  have h := erase_internal_deg (G:=G) (Dark D) z x
  obtain ⟨xn,xd⟩ := mem_erase.mp xm
  rw [←F.darkPart,bal,mem_union,mem_union,mem_singleton] at xd
  rcases xd with (ha|hb)|he
  · have p := F.strictA_local x ha
    omega
  · have p := F.strictB_local x hb
    omega
  exact (xn he).elim

#print axioms six_q1_left_slots
#print axioms six_q1_right_slots
#print axioms six_q1_common_slots
#print axioms six_q1_balance_port_slots
#print axioms six_q1_core_bounds
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
