import RootedOreTwoCandidates189
import DegreeFiveFourForeignGeom189
import DegreeFiveBothFiveResidual189
import WingSignature189


namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private inside_high_at_least_four_if_exclusive inside_high_at_least_three from DegreeFiveBalancedCommonRoot189
open private cut_mem_iff from DegreeFiveBothFiveResidual189
open private shore_connected from DegreeFiveActualCut189
open private lift_side_path from DegreeFiveSmallSides189
open ArticulationPair
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem free_port_route_of_missing_degree_sums
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (D : Cmp (G:=G) (a:=a) (b:=b))
    (D2 : 2≤(cutPorts D).card)
    (ore : ∀ u∈Shore D,∀ v∈Shore D,u≠v → ¬G.Adj u v → 5≤G.degree u → 5≤G.degree v →
      (Shore D).card≤(inside G (Shore D) u).card+(inside G (Shore D) v).card) :
    WingRealizes G a b (Shore D) .aFree ∨ WingRealizes G a b (Shore D) .bFree := by
  classical
  let S := Shore D
  let U := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let A : Finset U := univ.filter (fun u=>u.val∈cutPorts D)
  let high (u : U) := 5≤G.degree u.val
  have inA (u : U) : u∈A ↔ u.val∈cutPorts D := by simp [A]
  have size : A.card=(cutPorts D).card := by
    apply card_bij (fun u _=>u.val)
    · intro u h
      exact (inA u).mp h
    · intro u _ v _ e
      exact Subtype.ext e
    intro v vp
    exact ⟨⟨v,(cut_mem_iff.mp vp).1⟩,(inA _).mpr vp,rfl⟩
  have pair (u v : U) (uv : u≠v) : high u ∨ high v :=
    degree u.val v.val (fun e=>uv (Subtype.ext e))
  have cap (u v : U) (hu : high u) (hv : high v) (uv : u≠v)
      (no : ¬J.Adj u v) :
      Fintype.card U≤J.degree u+J.degree v := by
    have h := ore u.val u.property v.val v.property (fun e=>uv (Subtype.ext e)) no hu hv
    have n : Fintype.card U=S.card := Fintype.card_coe S
    rw [n]
    change S.card≤(G.induce (↑S : Set V)).degree u+(G.induce (↑S : Set V)).degree v
    rw [←inside_card_eq_degree_induce (G:=G) S u,←inside_card_eq_degree_induce (G:=G) S v]
    exact h
  obtain ⟨r,ra,t,p,pp,ps⟩ := rooted_Ore_from_two_candidates (shore_connected D) A (by omega) high pair cap
  have route : RouteOn G S r.val t.val := lift_side_path S p pp ps
  rcases (cut_mem_iff.mp ((inA r).mp ra)).2 with ar|br
  · exact .inl ⟨r.val,t.val,ar,route⟩
  exact .inr ⟨r.val,t.val,br,route⟩

theorem free_port_route_at_most_six
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {D : Cmp (G:=G) (a:=a) (b:=b)}
    (D2 : 2≤(cutPorts D).card) (small : (Shore D).card≤6) :
    WingRealizes G a b (Shore D) .aFree ∨ WingRealizes G a b (Shore D) .bFree := by
  apply free_port_route_of_missing_degree_sums degree D D2
  intro u us v vs _ _ hu hv
  have p := inside_high_at_least_three us hu
  have q := inside_high_at_least_three vs hv
  omega

private theorem inside_high_at_least_four_of_near_seven
    (hc : G.Connected) {C : Cmp (G:=G) (a:=a) (b:=b)} (size : (Shore C).card=7)
    (near : ∀ u∈sharedPortSet C,(secondShore C u).card≤1 ∧ ∀ v∈Shore C,G.dist u v≤2)
    {u : V} (uc : u∈Shore C) (uh : 5≤G.degree u) :
    4≤(inside G (Shore C) u).card := by
  classical
  let S := Shore C
  by_cases both : G.Adj a u ∧ G.Adj b u
  · have uk : u∈sharedPortSet C := mem_filter.mpr ⟨uc,both⟩
    obtain ⟨cap,dist⟩ := near u uk
    have sub : S.erase u \ inside G S u⊆secondShore C u := by
      intro v h
      obtain ⟨h,no⟩ := mem_sdiff.mp h
      obtain ⟨ne,vs⟩ := mem_erase.mp h
      have non : ¬G.Adj u v := fun e=>no (mem_filter.mpr ⟨vs,e⟩)
      have p := hc.one_lt_dist_of_ne_of_not_adj ne.symm non
      have q := dist v vs
      exact mem_inter.mpr ⟨vs,mem_filter.mpr ⟨mem_univ _,by omega⟩⟩
    have haveSub : inside G S u⊆S.erase u := by
      intro v h
      obtain ⟨vs,e⟩ := mem_filter.mp h
      exact mem_erase.mpr ⟨e.ne.symm,vs⟩
    have sum := card_sdiff_add_card_eq_card haveSub
    have le := card_le_card sub
    have ss : S.card=7 := size
    rw [card_erase_of_mem (show u∈S from uc)] at sum
    change 4≤(inside G S u).card
    omega
  exact inside_high_at_least_four_if_exclusive uc uh both

theorem free_port_route_at_near_seven
    (hc : G.Connected) (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)} (C2 : 2≤(cutPorts C).card) (size : (Shore C).card=7)
    (near : ∀ u∈sharedPortSet C,(secondShore C u).card≤1 ∧ ∀ v∈Shore C,G.dist u v≤2) :
    WingRealizes G a b (Shore C) .aFree ∨ WingRealizes G a b (Shore C) .bFree := by
  apply free_port_route_of_missing_degree_sums degree C C2
  intro u us v vs _ _ hu hv
  have p := inside_high_at_least_four_of_near_seven hc size near us hu
  have q := inside_high_at_least_four_of_near_seven hc size near vs hv
  omega

#print axioms free_port_route_at_most_six
#print axioms free_port_route_at_near_seven
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
