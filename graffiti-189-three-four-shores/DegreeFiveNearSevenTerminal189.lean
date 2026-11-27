import CliqueLowInsert189
import DegreeFiveThreeFourShapes189
import DegreeFiveFreeOreSmallNear189


namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private inside_high_at_least_four_if_exclusive inside_high_at_least_three from DegreeFiveBalancedCommonRoot189
open private cut_mem_iff from DegreeFiveBothFiveResidual189
open private shore_connected from DegreeFiveActualCut189
open private lift_side_path from DegreeFiveSmallSides189
open ArticulationPair
open private nonport_neighbors_subset from DegreeFiveThreeFiveShapes189
open private inside_high_at_least_four_of_near_seven from DegreeFiveFreeOreSmallNear189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem terminal_route_on_three_port_near_seven
    (hc : G.Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (min2 : ∀ u : V,2≤G.degree u)
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (C3 : (cutPorts C).card=3) (size : (Shore C).card=7)
    (near : ∀ u∈sharedPortSet C,(secondShore C u).card≤1 ∧ ∀ v∈Shore C,G.dist u v≤2)
    (lowNonport : ∀ z∈Shore C,¬5≤G.degree z → z∉cutPorts C)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    WingRealizes G a b (Shore C) .terminal := by
  classical
  let S := Shore C
  let U := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let A : Finset U := univ.filter (fun v=>5≤G.degree v.val)
  let H := completeWith J A
  letI : DecidableRel H.Adj := Classical.decRel _
  let xx : U := ⟨x,xc⟩
  have sub : J≤H := completeWith_mono J A
  have comp : CompleteOn H A := completeWith_of_mem J A
  have n : Fintype.card U=7 := (Fintype.card_coe S).trans size
  have portHigh {u : V} (up : u∈cutPorts C) : 5≤G.degree u := by
    apply Classical.byContradiction
    intro fail
    exact lowNonport u (cut_mem_iff.mp up).1 fail up
  have xxH : xx∈A := mem_filter.mpr ⟨mem_univ _,
    portHigh (mem_filter.mpr ⟨xc,.inl ax⟩)⟩
  have bound (u : U) (h : u∈A) : 4≤J.degree u := by
    change 4≤(G.induce (↑S : Set V)).degree u
    rw [←inside_card_eq_degree_induce (G:=G) S u]
    exact inside_high_at_least_four_of_near_seven hc size near u.property (mem_filter.mp h).2
  have cap (u v : U) (uv : H.Adj u v) (no : ¬J.Adj u v) :
      Fintype.card U+1≤J.degree u+J.degree v := by
    change J.Adj u v ∨ _ at uv
    obtain ⟨ua,va,_⟩ := uv.resolve_left no
    have p := bound u ua
    have q := bound v va
    omega
  have pack {t : V} (tp : t∈cutPorts C) (q : RouteOn H univ xx ⟨t,(cut_mem_iff.mp tp).1⟩) :
      WingRealizes G a b (Shore C) .terminal := by
    obtain ⟨p,pp,ps⟩ := q
    obtain ⟨q,qp,qs⟩ := terminal_ore_closure sub cap p pp (fun u=>(ps u).mpr (mem_univ _))
    have r : RouteOn G S x t := lift_side_path S q qp qs
    rcases (cut_mem_iff.mp tp).2 with at'|bt
    · exact ⟨t,x,at',bx,r.reverse⟩
    exact ⟨x,t,ax,bt,r⟩
  have pick (w : V) : ∃ t∈cutPorts C,t≠x ∧ t≠w := by
    apply Classical.byContradiction
    intro no
    have sub : cutPorts C⊆({x,w} : Finset V) := by
      intro t tp
      apply Classical.byContradiction
      intro h
      exact no ⟨t,tp,(fun e=>h (by simp [e])),(fun e=>h (by simp [e]))⟩
    have tally := card_le_card sub
    have le := card_insert_le x ({w} : Finset V)
    rw [card_singleton] at le
    omega
  by_cases low : ∃ z : U,¬5≤G.degree z.val
  · obtain ⟨z,zh⟩ := low
    have zP := lowNonport z.val z.property zh
    have ae : A=univ.erase z := by
      ext u
      change u∈univ.filter (fun w : U=>5≤G.degree w.val) ↔ _
      by_cases neq : u=z
      · simp [neq,zh]
      have uh := (degree u.val z.val (fun e=>neq (Subtype.ext e))).resolve_right zh
      simp [neq,uh]
    have zi : z∉A := by simp [ae]
    have h := min2 z.val
    obtain ⟨u,uN,v,vN,uv⟩ := one_lt_card.mp (show 1<(G.neighborFinset z.val).card by
      rw [card_neighborFinset_eq_degree]; omega)
    have uS := mem_of_mem_erase (nonport_neighbors_subset z.property zP uN)
    have vS := mem_of_mem_erase (nonport_neighbors_subset z.property zP vN)
    let uu : U := ⟨u,uS⟩
    let vv : U := ⟨v,vS⟩
    have zu := (mem_neighborFinset G z.val u).mp uN
    have zv := (mem_neighborFinset G z.val v).mp vN
    have ua : uu∈A := by simpa [ae] using (show uu≠z from fun h=>zu.ne.symm (congrArg Subtype.val h))
    have va : vv∈A := by simpa [ae] using (show vv≠z from fun h=>zv.ne.symm (congrArg Subtype.val h))
    have trail (t : V) (tp : t∈cutPorts C) (tx : t≠x)
        (avoid : ¬((x=u ∧ t=v) ∨ (x=v ∧ t=u))) :
        WingRealizes G a b (Shore C) .terminal := by
      apply pack tp
      let tt : U := ⟨t,(cut_mem_iff.mp tp).1⟩
      have tH : tt∈A := mem_filter.mpr ⟨mem_univ _,portHigh tp⟩
      have eq : insert z A=(univ : Finset U) := by rw [ae,insert_erase (mem_univ _)]
      have proof := clique_path_via_low H A comp zi xxH tH
        (fun e=>tx (congrArg Subtype.val e).symm) ua va
        (fun e=>uv (congrArg Subtype.val e)) (sub zu) (sub zv)
        (fun e=>avoid (e.imp (fun h=>⟨congrArg Subtype.val h.1,congrArg Subtype.val h.2⟩)
          (fun h=>⟨congrArg Subtype.val h.1,congrArg Subtype.val h.2⟩)))
      exact eq ▸ proof
    by_cases xu : x=u
    · obtain ⟨t,tp,tx,tv⟩ := pick v
      exact trail t tp tx (fun e=>e.elim (fun h=>tv h.2) (fun h=>uv (xu.symm.trans h.1)))
    obtain ⟨t,tp,tx,tu⟩ := pick u
    exact trail t tp tx (fun e=>e.elim (fun h=>xu h.1) (fun h=>tu h.2))
  obtain ⟨t,tp,tx,_⟩ := pick x
  let tt : U := ⟨t,(cut_mem_iff.mp tp).1⟩
  have tH : tt∈A := mem_filter.mpr ⟨mem_univ _,portHigh tp⟩
  have ae : A=(univ : Finset U) := by
    ext u
    have h : 5≤G.degree u.val := Classical.byContradiction (fun no=>low ⟨u,no⟩)
    simp [A,h]
  obtain ⟨q,qp,qs⟩ := path_between_in_clique A comp xxH tH
    (fun e=>tx (congrArg Subtype.val e).symm)
  exact pack tp (ae ▸ (show RouteOn H A xx tt from ⟨q,qp,qs⟩))

#print axioms terminal_route_on_three_port_near_seven
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
