import DegreeFiveActualCut189
import DegreeFiveDistanceTwoThreeClose189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private CutGraph Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- A distance-two root on one shore spends three even slots on itself and
the cut vertices. The union of the opposite cut shells, restricted to nonports,
must occupy distinct remaining slots at distance four from that root. -/
theorem opposite_near_nonports_le_three
    (hc : G.Connected) (two : G.dist a b = 2)
    (even : ∀ x, (EvenFrom G x).card ≤ 6)
    {C D : (CutGraph (G:=G) a b).ConnectedComponent} (cd : C ≠ D)
    {z : V} (zc : z ∈ Shore C) (za : G.dist z a = 2) (zb : G.dist z b = 2) :
    (((secondShore D a ∪ secondShore D b).filter
      (fun w => ¬ G.Adj a w ∧ ¬ G.Adj b w))).card ≤ 3 := by
  classical
  let W := (secondShore D a ∪ secondShore D b).filter
      (fun w => ¬ G.Adj a w ∧ ¬ G.Adj b w)
  have ab : a ≠ b := fun e => by rw [e, SimpleGraph.dist_self] at two; omega
  have za' : z ≠ a := fun e => (shore_off C).1 (Eq.mp (congrArg (fun v : V => v ∈ Shore C) e) zc)
  have zb' : z ≠ b := fun e => (shore_off C).2 (Eq.mp (congrArg (fun v : V => v ∈ Shore C) e) zc)
  have wd {w : V} (hw : w ∈ W) : w ∈ Shore D := by
    rcases mem_union.mp (mem_filter.mp hw).1 with ha|hb
    · exact (mem_inter.mp ha).1
    · exact (mem_inter.mp hb).1
  have nat2 {u w : V} (uw : u ≠ w) (n : ¬ G.Adj u w) : 2 ≤ G.dist u w := by
    have h := hc.pos_dist_of_ne uw
    have h' : G.dist u w ≠ 1 := fun eq => n (dist_eq_one_iff_adj.mp eq)
    omega
  have w4 {w : V} (hw : w ∈ W) : G.dist z w = 4 := by
    have hs := wd hw
    have wo := fun h => disjoint_left.mp (shore_disjoint cd) h hs
    have e := cross_metric (Shore C) hc zc wo (shore_closed C)
    rw [za, zb] at e
    have ap := nat2 (fun h => (shore_off D).1 (Eq.mp (congrArg (fun v : V => v ∈ Shore D) h.symm) hs)) (mem_filter.mp hw).2.1
    have bp := nat2 (fun h => (shore_off D).2 (Eq.mp (congrArg (fun v : V => v ∈ Shore D) h.symm) hs)) (mem_filter.mp hw).2.2
    rcases mem_union.mp (mem_filter.mp hw).1 with ha|hb
    · have q := (mem_filter.mp (mem_inter.mp ha).2).2
      omega
    · have q := (mem_filter.mp (mem_inter.mp hb).2).2
      omega
  have aoff : a ∉ W := fun h => (shore_off D).1 (wd h)
  have boff : b ∉ W := fun h => (shore_off D).2 (wd h)
  have zoff : z ∉ W := fun h => disjoint_left.mp (shore_disjoint cd) zc (wd h)
  have sub : insert z (insert a (insert b W)) ⊆ EvenFrom G z := by
    intro w hw
    simp only [mem_insert] at hw
    unfold EvenFrom
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rcases hw with rfl|rfl|rfl|hw
    · rw [SimpleGraph.dist_self]; decide
    · rw [za]; decide
    · rw [zb]; decide
    · rw [w4 hw]; decide
  have k := (card_le_card sub).trans (even z)
  rw [card_insert_of_not_mem (by simpa [za',zb'] using zoff),
    card_insert_of_not_mem (by simpa [ab] using aoff), card_insert_of_not_mem boff] at k
  change W.card ≤ 3
  omega

#print axioms opposite_near_nonports_le_three
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
