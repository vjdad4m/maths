import DegreeFiveBothAtLeastFour189
import DegreeFiveNonmixedThreeFour189
import DegreeFiveBothFiveResidual189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint shore_connected from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor from DegreeFiveThreeForeignImpossible189
open private cut_mem_iff from DegreeFiveBothFiveResidual189
open private local_shell_comes_from_port from DegreeFiveNonmixedThreeFour189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem missed_neighbor_is_unique_at_cap
    (hc : G.Connected) {D : Cmp (G:=G) (a:=a) (b:=b)} {x z : V}
    (near : ∀ t∈Shore D,G.dist x t≤2)
    (cap : (secondShore D x).card≤1)
    (zd : z∈Shore D) (xz : x≠z) (no : ¬G.Adj x z) :
    ∀ w∈Shore D,x≠w → w≠z → G.Adj x w := by
  classical
  have zm : z∈secondShore D x := by
    have lo := hc.one_lt_dist_of_ne_of_not_adj xz no
    have hi := near z zd
    exact mem_inter.mpr ⟨zd,by simp [DistanceTwo,show G.dist x z=2 by omega]⟩
  intro w wd xw wz
  apply Classical.byContradiction
  intro nw
  have wm : w∈secondShore D x := by
    have lo := hc.one_lt_dist_of_ne_of_not_adj xw nw
    have hi := near w wd
    exact mem_inter.mpr ⟨wd,by simp [DistanceTwo,show G.dist x w=2 by omega]⟩
  have h := one_lt_card.mpr ⟨w,wm,z,zm,wz⟩
  omega

/-- A shore whose ports are all common, near-universal up to a single
local distance-two defect, cannot hide a nonport from either cut. -/
theorem pure_shore_visible_from_first_cut
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (C4 : 4≤(cutPorts C).card) (D4 : 4≤(cutPorts D).card)
    (pure : ∀ x∈cutPorts D,G.Adj a x ∧ G.Adj b x)
    (near : ∀ x∈cutPorts D,(secondShore D x).card≤1 ∧
      ∀ w∈Shore D,G.dist x w≤2) :
    Shore D⊆cutPorts D ∪ secondShore D a := by
  classical
  intro z zd
  by_cases hp : z∈cutPorts D
  · exact mem_union_left _ hp
  apply mem_union_right
  apply Classical.byContradiction
  intro miss
  have za : ¬G.Adj a z := fun h=>hp (cut_mem_iff.mpr ⟨zd,.inl h⟩)
  have zb : ¬G.Adj b z := fun h=>hp (cut_mem_iff.mpr ⟨zd,.inr h⟩)
  have aNe : a≠z := fun e=>(shore_off D).1 (e.symm ▸ zd)
  have bNe : b≠z := fun e=>(shore_off D).2 (e.symm ▸ zd)
  have no {x : V} (xp : x∈cutPorts D) : ¬G.Adj x z := by
    intro xz
    exact miss (mem_inter.mpr ⟨zd,d2 hc aNe za (pure x xp).1 xz⟩)
  obtain ⟨x,xp⟩ := card_pos.mp (show 0<(cutPorts D).card by omega)
  have xd := (cut_mem_iff.mp xp).1
  have zx : z≠x := fun e=>hp (e.symm ▸ xp)
  let U := ↑(↑(Shore D) : Set V)
  obtain ⟨p⟩ := (shore_connected D).preconnected (⟨z,zd⟩ : U) ⟨x,xd⟩
  have hit : ∃ v∈Shore D,G.Adj z v := by
    cases p with
    | nil => exact (zx rfl).elim
    | @cons _ v _ e p => exact ⟨v.val,v.property,e⟩
  obtain ⟨v,vd,zv⟩ := hit
  have vPort : v∉cutPorts D := fun h=>no h zv.symm
  have touch {w : V} (wp : w∈cutPorts D) : G.Adj w v := by
    have wNe : w≠z := fun e=>hp (e ▸ wp)
    have wv : w≠v := fun e=>vPort (e ▸ wp)
    have wn := near w wp
    exact missed_neighbor_is_unique_at_cap hc wn.2 wn.1 zd wNe (no wp) v vd wv zv.ne.symm
  have localD : cutPorts D⊆DistanceTwo G z := by
    intro w wp
    have wz : z≠w := fun e=>hp (e.symm ▸ wp)
    exact d2 hc wz (fun e=>no wp e.symm) zv (touch wp).symm
  have phaseA : G.dist z a=3 := by
    have hi := G.dist_le (Walk.cons zv (.cons (touch xp).symm (.cons (pure x xp).1.symm .nil)))
    change G.dist z a≤3 at hi
    have low := hc.one_lt_dist_of_ne_of_not_adj aNe za
    have ne : G.dist a z≠2 := fun h=>miss (mem_inter.mpr ⟨zd,by simp [DistanceTwo,h]⟩)
    have comm := SimpleGraph.dist_comm (G:=G) (u:=z) (v:=a)
    omega
  have phaseB : G.dist z b=3 := by
    have hi := G.dist_le (Walk.cons zv (.cons (touch xp).symm (.cons (pure x xp).2.symm .nil)))
    change G.dist z b≤3 at hi
    have low := hc.one_lt_dist_of_ne_of_not_adj bNe zb
    have ne : G.dist b z≠2 := by
      intro zz
      obtain ⟨w,wp,wz⟩ := local_shell_comes_from_port hc two (.inr rfl)
        (show z∈secondShore D b from mem_inter.mpr ⟨zd,by simp [DistanceTwo,zz]⟩)
      exact no (cut_mem_iff.mpr ⟨(mem_filter.mp wp).1,.inr (mem_filter.mp wp).2⟩) wz
    have comm := SimpleGraph.dist_comm (G:=G) (u:=z) (v:=b)
    omega
  have across : cutPorts C⊆EvenFrom G z := by
    intro w wp
    obtain ⟨wc,hit⟩ := cut_mem_iff.mp wp
    have out : w∉Shore D := fun h=>disjoint_left.mp (shore_disjoint cd) wc h
    have eq := cross_metric (Shore D) hc zd out (shore_closed D)
    rw [phaseA,phaseB] at eq
    have posA := hc.pos_dist_of_ne (show a≠w from fun e=>(shore_off C).1 (e.symm ▸ wc))
    have posB := hc.pos_dist_of_ne (show b≠w from fun e=>(shore_off C).2 (e.symm ▸ wc))
    have exactFour : G.dist z w=4 := by
      rcases hit with aw|bw
      · have n := dist_eq_one_iff_adj.mpr aw
        omega
      have n := dist_eq_one_iff_adj.mpr bw
      omega
    unfold EvenFrom
    exact mem_filter.mpr ⟨mem_univ _,by rw [exactFour]; decide⟩
  have loc : cutPorts D⊆EvenFrom G z := by
    intro w wm
    have fact := (mem_filter.mp (localD wm)).2
    unfold EvenFrom
    exact mem_filter.mpr ⟨mem_univ _,by rw [fact]; decide⟩
  have dis : Disjoint (cutPorts C) (cutPorts D) :=
    (shore_disjoint cd).mono (filter_subset _ _) (filter_subset _ _)
  have n := (card_le_card (union_subset across loc)).trans (even z)
  rw [card_union_of_disjoint dis] at n
  omega

#print axioms pure_shore_visible_from_first_cut
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
