import DegreeFiveThreeThreeDarkOrders189
import SmallDenseRoute189







namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint shore_nonempty shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp two_shore_budget count_cut_degree_on_two_shores portColor from DegreeFiveThreeForeignImpossible189
open private four_in_nonsingleton second_positive_of_small_ports anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private nonport_neighbors_subset nonport_degree_bound_small from DegreeFiveThreeFiveShapes189
open private nonport_mem_second_iff_neighbor_port from DegreeFiveOneFiveFarProfile189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

open private boundary_has_at_least_two dark dark_boundary_is_visible visible_in_nonports
  from DegreeFiveTwoThreeBase189

open private firstDark firstDark_iff_distance_three dark_dist_ge_three cross_ports_at_distance_two
  distance_two_at_cut_lower from DegreeFiveTwoThreeVisTwo189
open private visible_at_least_two_of_dark from DegreeFiveTwoThreeBase189

open ArticulationPair

private theorem visible_touches_some_port
    (hc : G.Connected) {C : Cmp (G:=G) (a:=a) (b:=b)}
    (allC : ∀ z∈cutPorts C,G.Adj a z) {v : V} (vv : v∈secondShore C a) :
    ∃ p∈cutPorts C,G.Adj p v := by
  obtain ⟨vc,vp⟩ := mem_sdiff.mp (visible_in_nonports allC vv)
  obtain ⟨p,pc,vp'⟩ := (nonport_mem_second_iff_neighbor_port hc vc vp (.inl rfl)).mp vv
  obtain ⟨ps,ap⟩ := mem_filter.mp pc
  exact ⟨p,mem_filter.mpr ⟨ps,.inl ap⟩,vp'.symm⟩

private theorem all_high_port_neighborhood
    (hc : G.Connected) {C : Cmp (G:=G) (a:=a) (b:=b)}
    (C3 : (cutPorts C).card=3) (allC : ∀ z∈cutPorts C,G.Adj a z)
    {p v : V} (pp : p∈cutPorts C) (p5 : 5≤G.degree p)
    (_vA : v∈secondShore C a) (_pv : G.Adj p v)
    (unique : ∀ w∈secondShore C a,G.Adj p w → w=v) :
    G.neighborFinset p=insert a (insert b (insert v ((cutPorts C).erase p))) := by
  classical
  let E := (cutPorts C).erase p
  let S := insert a (insert b (insert v E))
  have sub : G.neighborFinset p⊆S := by
    intro w hm
    have e := (mem_neighborFinset G p w).mp hm
    rcases shore_closed C p (mem_filter.mp pp).1 w e with wa|wb|wc
    · simp [S,wa]
    · simp [S,wb]
    by_cases wp : w∈cutPorts C
    · exact mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨e.ne.symm,wp⟩)))
    have wv := (nonport_mem_second_iff_neighbor_port hc wc wp (.inl rfl)).mpr
      ⟨p,mem_filter.mpr ⟨(mem_filter.mp pp).1,allC p pp⟩,e.symm⟩
    simp [S,unique w wv e]
  have t := card_insert_le a (insert b (insert v E))
  have u := card_insert_le b (insert v E)
  have w := card_insert_le v E
  have e2 : E.card=2 := by change ((cutPorts C).erase p).card=2; rw [card_erase_of_mem pp,C3]
  apply eq_of_subset_of_card_le sub
  rw [card_neighborFinset_eq_degree]
  change (insert a (insert b (insert v E))).card≤G.degree p
  omega

private theorem high_visible_neighborhood
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (allC : ∀ z∈cutPorts C,G.Adj a z) (A3 : (secondShore C a).card=3)
    (high : ∀ z∈Shore C,5≤G.degree z) {v p : V}
    (vv : v∈secondShore C a) (_pp : p∈cutPorts C)
    (sole : ∀ q∈cutPorts C,G.Adj v q → q=p)
    (atMost : ((dark C).filter (G.Adj v)).card≤2) :
    ((dark C).filter (G.Adj v)).card=2 ∧
      ∀ w∈secondShore C a,v≠w → G.Adj v w := by
  classical
  let A := secondShore C a
  let S := insert p ((A.erase v)∪(dark C).filter (G.Adj v))
  obtain ⟨vc,vp⟩ := mem_sdiff.mp (visible_in_nonports allC vv)
  have sub : G.neighborFinset v⊆S := by
    intro w h
    have vw := (mem_neighborFinset G v w).mp h
    obtain ⟨wn,wc⟩ := mem_erase.mp (nonport_neighbors_subset vc vp h)
    by_cases wp : w∈cutPorts C
    · exact mem_insert.mpr (.inl (sole w wp vw))
    by_cases wa : w∈A
    · exact mem_insert_of_mem (mem_union_left _ (mem_erase.mpr ⟨wn,wa⟩))
    exact mem_insert_of_mem (mem_union_right _ (mem_filter.mpr
      ⟨mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨wc,wp⟩,wa⟩,vw⟩))
  have x := (card_le_card sub)
  rw [card_neighborFinset_eq_degree] at x
  have h := high v vc
  have a2 : (A.erase v).card=2 := by
    rw [card_erase_of_mem (show v∈A from vv)]
    have t : A.card=3 := A3
    omega
  have q := card_union_le (A.erase v) ((dark C).filter (G.Adj v))
  have z := card_insert_le p ((A.erase v)∪(dark C).filter (G.Adj v))
  have tally : S.card≤(A.erase v).card+((dark C).filter (G.Adj v)).card+1 := by
    change (insert p ((A.erase v)∪(dark C).filter (G.Adj v))).card≤_
    omega
  have e : G.neighborFinset v=S := eq_of_subset_of_card_le sub (by
    rw [card_neighborFinset_eq_degree]
    omega)
  refine ⟨by omega,?_⟩
  intro w wa ne
  have ws : w∈S := mem_insert_of_mem (mem_union_left _ (mem_erase.mpr ⟨ne.symm,wa⟩))
  exact (mem_neighborFinset G v w).mp (e.symm ▸ ws)

#print axioms all_high_port_neighborhood
#print axioms high_visible_neighborhood
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
