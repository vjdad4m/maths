import DegreeFiveOneFiveCapGlue189
import SmallFiveCap189
import DegreeFiveFreeOreSmallNear189




namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset Graffiti189Ore ArticulationPair
open private inside_high_at_least_three inside_high_at_least_four_if_exclusive from DegreeFiveBalancedCommonRoot189
open private Shore shore_off shore_closed shore_disjoint shore_nonempty shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private singleton_shore_of_one_port from DegreeFiveOneFourShapes189
open private two_walk_middle from DistanceTwoCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp two_shore_budget count_cut_degree_on_two_shores portColor from DegreeFiveThreeForeignImpossible189
open private four_in_nonsingleton from DegreeFiveDistanceTwoThreeClose189
open private nonport_neighbors_subset from DegreeFiveThreeFiveShapes189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem traceable_of_actual_five_one_five_ports_small
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (one : (cutPorts C).card=1) (five : (cutPorts D).card=5)
    (small : (Shore D).card≤10) :
    ∃ x y,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨r,ce,ar,br,high,colors⟩ := one_five_shore_shape two conn degree cd cover one five
  have ab : a≠b := by intro h; rw [h,dist_self] at two; omega
  by_cases tiny : (Shore D).card≤6
  · have mid : WingRealizes G a b (Shore C) .terminal := by
      rw [ce]
      exact ⟨r,r,ar,br,RouteOn.singleton⟩
    have f := free_port_route_at_most_six degree (show 2≤(cutPorts D).card by omega) tiny
    exact traceable_of_complementary_wings ab (shore_disjoint cd) (shore_off C).1 (shore_off C).2
      (shore_off D).1 (shore_off D).2 cover (.inl ⟨mid,f⟩)
  apply traceable_from_one_five_cap ab cd cover five ce ar br colors
  let S := Shore D
  let U := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let P : Finset U := univ.filter (fun u=>u.val∈cutPorts D)
  have ps (u : U) : u∈P ↔ u.val∈cutPorts D := by simp [P]
  have p5 : P.card=5 := by
    rw [←five]
    apply card_bij (fun u _=>u.val)
    · intro u h; exact (ps u).mp h
    · intro u _ v _ e; exact Subtype.ext e
    intro w wp
    exact ⟨⟨w,(mem_filter.mp wp).1⟩,(ps _).mpr wp,rfl⟩
  have n : Fintype.card U=S.card := Fintype.card_coe S
  have nL : 7≤Fintype.card U := by
    have lo : ¬S.card≤6 := tiny
    omega
  have h3 (u : U) (_ : u∈P) : 3≤J.degree u := by
    change 3≤(G.induce (↑S : Set V)).degree u
    rw [←inside_card_eq_degree_induce (G:=G) S u]
    exact inside_high_at_least_three u.property (high u.val u.property)
  have h5 (u : U) (no : u∉P) : 5≤J.degree u := by
    change 5≤(G.induce (↑S : Set V)).degree u
    rw [←inside_card_eq_degree_induce (G:=G) S u]
    have sub := nonport_neighbors_subset u.property (fun h=>no ((ps u).mpr h))
    have sub' : G.neighborFinset u.val⊆inside G S u.val := fun w hw=>
      mem_filter.mpr ⟨mem_of_mem_erase (sub hw),(mem_neighborFinset G u.val w).mp hw⟩
    have q := card_le_card sub'
    rw [card_neighborFinset_eq_degree] at q
    exact (high u.val u.property).trans q
  change Graffiti189Ore.Traceable (cap J (fun u : U=>u.val∈cutPorts D))
  have predicate : (fun u : U=>u.val∈cutPorts D)=(fun u : U=>u∈P) :=
    funext (fun u=>propext ((ps u).symm))
  rw [predicate]
  apply traceable_cap_small_five_contacts P p5 nL h3 h5
  by_cases cap9 : (Shore D).card≤9
  · exact .inl (n.trans_le cap9)
  have n10 : Fintype.card U=10 := by
    have s : S.card≤10 := small
    have m : ¬S.card≤9 := cap9
    omega
  have bound := (one_five_opposite_order_bound hc two even conn degree cd cover one five).2
  have own (c : V) (cc : c=a ∨ c=b) : ∃ u∈cutPorts D,¬G.Adj c u := by
    apply Classical.byContradiction
    intro no
    apply cap9
    exact bound ⟨c,cc,fun u up=>Classical.byContradiction (fun n=>no ⟨u,up,n⟩)⟩
  obtain ⟨x,xp,xa⟩ := own a (.inl rfl)
  obtain ⟨y,yp,yb⟩ := own b (.inr rfl)
  have xy : x≠y := by
    intro eq
    exact (mem_filter.mp xp).2.elim xa (fun h=>yb (eq ▸ h))
  let xx : U := ⟨x,(mem_filter.mp xp).1⟩
  let yy : U := ⟨y,(mem_filter.mp yp).1⟩
  let E : Finset U := {xx,yy}
  have pp : E⊆P := insert_subset_iff.mpr ⟨(ps _).mpr xp,singleton_subset_iff.mpr ((ps _).mpr yp)⟩
  have size : E.card=2 := by
    have ne : xx≠yy := fun h=>xy (congrArg Subtype.val h)
    simp [E,ne]
  refine .inr ⟨n10,E,pp,size,?_⟩
  intro u ue
  change 4≤(G.induce (↑S : Set V)).degree u
  rw [←inside_card_eq_degree_induce (G:=G) S u]
  apply inside_high_at_least_four_if_exclusive u.property (high u.val u.property)
  have h : u=xx ∨ u=yy := by simpa [E] using ue
  rcases h with h|h
  · intro p
    have eq : u.val=x := congrArg Subtype.val h
    exact xa (eq ▸ p.1)
  intro p
  have eq : u.val=y := congrArg Subtype.val h
  exact yb (eq ▸ p.2)

#print axioms traceable_of_actual_five_one_five_ports_small
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
