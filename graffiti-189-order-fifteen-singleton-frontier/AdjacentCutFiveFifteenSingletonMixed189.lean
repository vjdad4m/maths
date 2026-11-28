import AdjacentCutFiveFifteenSingletonSeparator189
import AdjacentCutFiveFourteenSingletonTerminal189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_off shore_closed shore_disjoint from AdjacentCutFiveActual189
open private key classSet key_facts from AdjacentCutFiveTopProfiles189
open private key_a_port key_b_port from AdjacentCutFiveTopFlatten189
open private predecessor_of_positive_dist left_even_adjoins_exclusive from AdjacentCutFiveSixteenSingletonDepth189
open private even_two_three_info restrict_unique_profile cannot_fit_four_and_two_more from AdjacentCutFiveSixteenSingletonGeometry189
open private nonedge_of_right_port_four_dark_neighbors disconnected_remove_two_of_dark_exclusive_no_edges
  from AdjacentCutFiveFifteenSingletonSeparator189
open private d2 mem_positive from AdjacentCutFiveBound189
open private positive_cap foreign_pos_even from AdjacentCutFiveComponents189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem right_even_has_actual_b_port
    (hc : G.Connected) (ab : G.Adj a b) {D : Cmp G a b} {w : V}
    (wd : w∈Shore D) (da : G.dist a w=3) (db : G.dist b w=2) :
    ∃ t∈classSet D 4,G.Adj b t ∧ ¬G.Adj a t ∧ G.Adj t w := by
  have p : 0<G.dist w b := by rw [dist_comm,db]; decide
  obtain ⟨t,wt,tb⟩ := predecessor_of_positive_dist hc p
  have tdb : G.dist b t=1 := by
    rw [dist_comm (G:=G) (u:=w) (v:=b),dist_comm (G:=G) (u:=t) (v:=b),db] at tb
    omega
  have tda : G.dist a t≥2 := by
    have z := hc.dist_triangle (u:=a) (v:=t) (w:=w)
    rw [da,dist_eq_one_iff_adj.mpr wt.symm] at z
    omega
  have td : t∈Shore D := by
    rcases shore_closed D _ wd _ wt with rfl|rfl|h
    · rw [dist_self] at tda; omega
    · rw [dist_self] at tdb; omega
    · exact h
  have tda2 : G.dist a t=2 := by
    have z := hc.dist_triangle (u:=a) (v:=b) (w:=t)
    rw [dist_eq_one_iff_adj.mpr ab,tdb] at z
    omega
  have k : key G a b t=4 := by classical simp [key,tda2,tdb]
  refine ⟨t,mem_filter.mpr ⟨td,k⟩,dist_eq_one_iff_adj.mp tdb,?_,wt.symm⟩
  intro at'
  have h := dist_eq_one_iff_adj.mpr at'
  omega

#print axioms right_even_has_actual_b_port

private theorem all_common_of_adjacent_singleton_profile_two
    (hc : G.Connected) (ab : G.Adj a b)
    {D : Cmp G a b} (atleast : 3≤((Shore D).filter (G.Adj a)).card)
    (one : (classSet D 3).card=1) (two : (classSet D 5).card=2) :
    ∀ w∈classSet D 5,G.Adj a w ∧ G.Adj b w := by
  classical
  let T := (Shore D).filter (G.Adj a)
  have sub : T⊆ classSet D 3 ∪ classSet D 5 := by
    intro w hw
    have ⟨wd,aw⟩ := mem_filter.mp hw
    have wb : w≠b := fun eq=>(shore_off D).2 (eq ▸ wd)
    rcases key_a_port hc ab wb aw with m|m
    · exact mem_union_left _ (mem_filter.mpr ⟨wd,m⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨wd,m⟩)
  have card' := card_union_le (classSet D 3) (classSet D 5)
  rw [one,two] at card'
  have eq := eq_of_subset_of_card_le sub (card'.trans atleast)
  intro w wm
  have wt : w∈T := eq ▸ mem_union_right (classSet D 3) wm
  have aw := (mem_filter.mp wt).2
  have k := (mem_filter.mp wm).2
  obtain ⟨dA,dB,_⟩ := key_facts hc ab w
  rw [k] at dA dB
  change G.dist a w=depth G a b w+0 at dA
  change G.dist b w=depth G a b w+0 at dB
  exact ⟨aw,dist_eq_one_iff_adj.mp (dB.trans (dA.symm.trans (dist_eq_one_iff_adj.mpr aw)))⟩

#print axioms all_common_of_adjacent_singleton_profile_two

private theorem separator_of_only_one_actual_b_at_mixed_profile
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ z,(EvenFrom G z).card≤6)
    {C D : Cmp G a b} (cd : C≠D) {s : V} (sc : s∈Shore C) (as' : G.Adj a s)
    (zer : (classSet D 2).card=0) (four : (classSet D 1).card=4)
    {x y : V} (xd : x∈Shore D) (yd : y∈Shore D)
    (ax : G.Adj a x) (nx : ¬G.Adj b x) (by' : G.Adj b y) (ny : ¬G.Adj a y)
    (LA : classSet D 3={x})
    (RB : ∀ z∈classSet D 4, G.Adj b z → z=y)
    (dists : ∀ w∈classSet D 1,G.dist a w=3 ∧ G.dist b w=2) :
    ∃ u v : V,u≠v ∧ ¬G.Adj u v ∧ ¬(G.induce {z : V | z≠u ∧ z≠v}).Connected := by
  classical
  have allY : ∀ w∈classSet D 1,G.Adj y w := by
    intro w wm
    obtain ⟨t,tm,bt,_,tw⟩ := right_even_has_actual_b_port hc ab (mem_filter.mp wm).1 (dists w wm).1 (dists w wm).2
    exact RB t tm bt ▸ tw
  have xy : x≠y := fun e=>ny (e ▸ ax)
  have nxy := nonedge_of_right_port_four_dark_neighbors hc ab even cd sc as' xd ax nx allY four.ge
    (fun w m=>(dists w m).1)
  obtain ⟨w,wm⟩ := card_pos.mp (show 0<(classSet D 1).card by omega)
  have dw := dists w wm
  have dark : w∈Shore D ∧ ¬G.Adj a w ∧ ¬G.Adj b w :=
    ⟨(mem_filter.mp wm).1,fun h=>by have e := dist_eq_one_iff_adj.mpr h; omega,
      fun h=>by have e := dist_eq_one_iff_adj.mpr h; omega⟩
  refine ⟨x,y,xy,nxy,disconnected_remove_two_of_dark_exclusive_no_edges hc cd sc zer xd yd (.inl ax) (.inr by') dark ?_⟩
  intro z zd zx zy h
  have za : z≠a := fun e=>(shore_off D).1 (e ▸ zd)
  have zb : z≠b := fun e=>(shore_off D).2 (e ▸ zd)
  rcases h with ⟨az,nz⟩|⟨bz,nz⟩
  · have k : key G a b z=3 := by
      have db := (mem_filter.mp (d2 hc zb.symm nz ab.symm az)).2
      simp [key,dist_eq_one_iff_adj.mpr az,db]
    have zm : z∈classSet D 3 := mem_filter.mpr ⟨zd,k⟩
    exact (zx (by simpa [LA] using zm)).elim
  · have k : key G a b z=4 := by
      have da := (mem_filter.mp (d2 hc za.symm nz ab bz)).2
      simp [key,dist_eq_one_iff_adj.mpr bz,da]
    exact (zy (RB z (mem_filter.mpr ⟨zd,k⟩) bz)).elim

#print axioms separator_of_only_one_actual_b_at_mixed_profile
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
