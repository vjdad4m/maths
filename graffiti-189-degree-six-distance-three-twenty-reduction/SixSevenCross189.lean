import SixSevenGeometry189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_disjoint shore_off shore_closed shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private no_common_far from SixDistanceThreeShort189
open FiveAdjacent (cross_metric)
set_option linter.unusedSectionVars false
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {C D : Cmp G a b}

theorem unseen_nonport_ge_three (hc : G.Connected) {r x : V}
    (rx : r≠x) (no : ¬G.Adj r x) (not2 : G.dist r x≠2) : 3≤G.dist r x := by
  have h := hc.one_lt_dist_of_ne_of_not_adj rx no
  omega

theorem opposite_unseen_cross_four (hc : G.Connected)
    (far : 3≤G.dist a b) (ab : a≠b) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cd : C≠D) (seven : (Shore C).card=7) (eleven : (Shore D).card=11)
    {x y : V} (xd : x∈Shore D) (yc : y∈Shore C) (xh : 6≤G.degree x)
    (ax : G.Adj a x) (by' : G.Adj b y)
    (xn : G.dist b x≠2) (yn : G.dist a y≠2) : G.dist x y=4 := by
  have xa1 := dist_eq_one_iff_adj.mpr ax
  have yb1 := dist_eq_one_iff_adj.mpr by'
  have xb : x≠b := fun e=>(shore_off D).2 (e ▸ xd)
  have ya : y≠a := fun e=>(shore_off C).1 (e ▸ yc)
  have xnb : ¬G.Adj b x := fun e=> no_common_far far ⟨ax,e⟩
  have yna : ¬G.Adj a y := fun e=> no_common_far far ⟨e,by'⟩
  have x3 := unseen_nonport_ge_three hc xb.symm xnb xn
  have y3 := unseen_nonport_ge_three hc ya.symm yna yn
  obtain ⟨r,rc,ar⟩ := shore_hit_a ab conn C
  obtain ⟨s,sd,bs⟩ := shore_hit_b ab conn D
  have rs : r≠s := fun e=>disjoint_left.mp (shore_disjoint cd) rc (e ▸ sd)
  have yD : y∉Shore D := fun ym=>disjoint_left.mp (shore_disjoint cd) yc ym
  rw [cross_metric (Shore D) hc xd yD (shore_closed D),dist_comm (u:=x) (v:=a),
    dist_comm (u:=x) (v:=b),xa1,yb1]
  rcases degree r s rs with rh|sh
  · have z := unseen_dist_three_of_charged_port hc ya yc ar yna yn
      (fun e ne=>seven_nonedge_to_high_is_distance_two hc far conn seven rc yc e.symm ne rh)
    omega
  · have z := unseen_dist_three_of_charged_port hc xb xd bs xnb xn
      (fun e ne=>eleven_nonedge_charges hc far eleven sd xd e.symm ne sh xh)
    omega

theorem unseen_dark_cross_four (hc : G.Connected)
    (far : 3≤G.dist a b) (ab : a≠b) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cd : C≠D) (seven : (Shore C).card=7) {x y : V}
    (xd : x∈Shore D) (yc : y∈Shore C) (ax : G.Adj a x)
    (yna : ¬G.Adj a y) (ynb : ¬G.Adj b y) (yn : G.dist a y≠2) :
    G.dist x y=4 := by
  have ya : y≠a := fun e=>(shore_off C).1 (e ▸ yc)
  have yb : y≠b := fun e=>(shore_off C).2 (e ▸ yc)
  have xb : x≠b := fun e=>(shore_off D).2 (e ▸ xd)
  have xnb : ¬G.Adj b x := fun e=>no_common_far far ⟨ax,e⟩
  obtain ⟨r,rc,ar⟩ := shore_hit_a ab conn C
  have yr : y≠r := fun e=>yna (e.symm ▸ ar)
  have yr0 : ¬G.Adj r y := fun e=>yn ((mem_cutSeen.mp (visible_of_adj_port hc ya yc ar e yna)).2)
  have yl : ¬6≤G.degree y := fun yh=>yr0 (dark_high_universal_in_seven seven yc yna ynb yh r rc yr.symm).symm
  have rh := (degree r y yr.symm).resolve_right yl
  have eq := unseen_dist_three_of_charged_port hc ya yc ar yna yn
    (fun e ne=>seven_nonedge_to_high_is_distance_two hc far conn seven rc yc e.symm ne rh)
  have xlo := hc.one_lt_dist_of_ne_of_not_adj xb.symm xnb
  have ylo := hc.one_lt_dist_of_ne_of_not_adj yb.symm ynb
  have yD : y∉Shore D := fun ym=>disjoint_left.mp (shore_disjoint cd) yc ym
  rw [cross_metric (Shore D) hc xd yD (shore_closed D),dist_comm (u:=x) (v:=a),
    dist_comm (u:=x) (v:=b),dist_eq_one_iff_adj.mpr ax,eq]
  omega

theorem both_seen_dark_cross_four (hc : G.Connected) (cd : C≠D)
    {x y : V} (xd : x∈Shore D) (yc : y∈Shore C)
    (xa : G.dist a x=2) (xb : G.dist b x=2)
    (ya : G.dist a y=2) (yb : G.dist b y=2) : G.dist x y=4 := by
  have yD : y∉Shore D := fun ym=>disjoint_left.mp (shore_disjoint cd) yc ym
  rw [cross_metric (Shore D) hc xd yD (shore_closed D),dist_comm (u:=x) (v:=a),
    dist_comm (u:=x) (v:=b),xa,xb,ya,yb]
  omega

#print axioms opposite_unseen_cross_four
#print axioms unseen_dark_cross_four
#print axioms both_seen_dark_cross_four
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
