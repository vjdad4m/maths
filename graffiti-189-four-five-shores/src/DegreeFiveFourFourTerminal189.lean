import DegreeFiveBothFiveResidual189
import TerminalOreClosure189
import WingSignature189
import DegreeFiveNearPortEight189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_connected from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private cut_mem_iff from DegreeFiveBothFiveResidual189
open private inside_high_at_least_four_if_exclusive inside_high_at_least_three from DegreeFiveBalancedCommonRoot189
open private lift_side_path from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- At most seven vertices, all globally high: the finite shore itself
has enough degree for a terminal-preserving Ore completion. -/
theorem terminal_mask_of_high_four_port_shore
    (hc : G.Connected) {C : Cmp (G:=G) (a:=a) (b:=b)}
    (four : (cutPorts C).card=4) (small : (Shore C).card≤7)
    (high : ∀ u∈Shore C,5≤G.degree u)
    (near : ∀ u∈sharedPortSet C,(secondShore C u).card≤1 ∧ ∀ v∈Shore C,G.dist u v≤2)
    {x : V} (xs : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    WingRealizes G a b (Shore C) .terminal := by
  classical
  let S := Shore C
  let U := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let H := completeWith J (univ : Finset U)
  letI : DecidableRel H.Adj := Classical.decRel _
  have sizeU : Fintype.card U=S.card := Fintype.card_coe S
  have small' : S.card≤7 := small
  have bound3 (u : U) : 3≤J.degree u := by
    change 3≤(G.induce (↑S : Set V)).degree u
    rw [←inside_card_eq_degree_induce (G:=G) S u]
    exact inside_high_at_least_three u.property (high u.val u.property)
  have bound4 (u : U) (big : 6≤S.card) : 4≤J.degree u := by
    by_cases both : G.Adj a u.val ∧ G.Adj b u.val
    · have uk : u.val∈sharedPortSet C := mem_filter.mpr ⟨u.property,both⟩
      obtain ⟨cap,dist⟩ := near u.val uk
      have sub : S.erase u.val \ inside G S u.val⊆secondShore C u.val := by
        intro v h
        obtain ⟨h,no⟩ := mem_sdiff.mp h
        obtain ⟨ne,vs⟩ := mem_erase.mp h
        have non : ¬G.Adj u.val v := fun e=>no (mem_filter.mpr ⟨vs,e⟩)
        have positive := hc.pos_dist_of_ne ne.symm
        have not1 : G.dist u.val v≠1 := fun e=>non (dist_eq_one_iff_adj.mp e)
        have le2 := dist v vs
        exact mem_inter.mpr ⟨vs,mem_filter.mpr ⟨mem_univ _,by omega⟩⟩
      have haveSub : inside G S u.val⊆S.erase u.val := by
        intro v h
        obtain ⟨vs,e⟩ := mem_filter.mp h
        exact mem_erase.mpr ⟨e.ne.symm,vs⟩
      have sum := card_sdiff_add_card_eq_card haveSub
      have le := card_le_card sub
      rw [card_erase_of_mem (show u.val∈S from u.property)] at sum
      change 4≤(G.induce (↑S : Set V)).degree u
      rw [←inside_card_eq_degree_induce (G:=G) S u]
      omega
    change 4≤(G.induce (↑S : Set V)).degree u
    rw [←inside_card_eq_degree_induce (G:=G) S u]
    exact inside_high_at_least_four_if_exclusive u.property (high u.val u.property) both
  have cap (u v : U) (_ : H.Adj u v) (_ : ¬J.Adj u v) :
      Fintype.card U+1≤J.degree u+J.degree v := by
    by_cases big : 6≤S.card
    · have h := bound4 u big
      have k := bound4 v big
      omega
    have h := bound3 u
    have k := bound3 v
    omega
  have other : ∃ y∈cutPorts C,y≠x := by
    apply Classical.byContradiction
    intro h
    have sub : cutPorts C⊆{x} := fun y yp=>mem_singleton.mpr
      (Classical.byContradiction (fun e=>h ⟨y,yp,e⟩))
    have q := card_le_card sub
    rw [four,card_singleton] at q
    omega
  obtain ⟨y,yp,yx⟩ := other
  let xx : U := ⟨x,xs⟩
  let yy : U := ⟨y,(cut_mem_iff.mp yp).1⟩
  obtain ⟨p,pp,ps⟩ := path_between_in_clique (univ : Finset U)
    (completeWith_of_mem J _) (mem_univ xx) (mem_univ yy)
    (fun h=>yx (congrArg Subtype.val h).symm)
  obtain ⟨q,qp,qs⟩ := terminal_ore_closure (completeWith_mono J _) cap p pp
    (fun w=>(ps _).mpr (mem_univ _))
  have route : RouteOn G S x y := lift_side_path S q qp qs
  rcases (cut_mem_iff.mp yp).2 with ay|by'
  · exact ⟨y,x,ay,bx,route.reverse⟩
  exact ⟨x,y,ax,by',route⟩

/-- On four all-port vertices at most one is exclusive; every spanning
route then has compatible terminal colors. -/
theorem terminal_mask_of_very_small_four_port_shore
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (four : (cutPorts C).card=4) (size : (Shore C).card=4) :
    WingRealizes G a b (Shore C) .terminal := by
  classical
  let S := Shore C
  have s4 : S.card=4 := size
  have allP : cutPorts C=S := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have adjAll {u : V} (us : u∈S) (u5 : 5≤G.degree u) :
      (G.Adj a u ∧ G.Adj b u) ∧ ∀ v∈S,u≠v → G.Adj u v := by
    have sub : inside G S u⊆S.erase u := by
      intro t tm
      obtain ⟨ts,e⟩ := mem_filter.mp tm
      exact mem_erase.mpr ⟨e.ne.symm,ts⟩
    have cap := card_le_card sub
    rw [card_erase_of_mem us] at cap
    have shared : G.Adj a u ∧ G.Adj b u := by
      apply Classical.byContradiction
      intro h
      have lower : 4≤(inside G S u).card := inside_high_at_least_four_if_exclusive us u5 h
      omega
    have lower : 3≤(inside G S u).card := inside_high_at_least_three us u5
    have eq : inside G S u=S.erase u := eq_of_subset_of_card_le sub (by
      rw [card_erase_of_mem us]
      omega)
    refine ⟨shared,?_⟩
    intro w ws uw
    have t : w∈inside G S u := by rw [eq]; exact mem_erase.mpr ⟨uw.symm,ws⟩
    exact (mem_filter.mp t).2
  have cl : CompleteOn G S := by
    intro u us v vs uv
    rcases degree u v uv with hu|hv
    · exact (adjAll us hu).2 v vs uv
    exact ((adjAll vs hv).2 u us uv.symm).symm
  obtain ⟨v,vs,w,ws,vw⟩ := one_lt_card.mp (show 1<S.card by omega)
  obtain ⟨q,qp,qs⟩ := path_between_in_clique S cl vs ws vw
  have p : RouteOn G S v w := ⟨q,qp,qs⟩
  have vp : v∈cutPorts C := allP.symm ▸ vs
  have wp : w∈cutPorts C := allP.symm ▸ ws
  rcases degree v w vw with vh|wh
  · obtain ⟨av,bv⟩ := (adjAll vs vh).1
    rcases (cut_mem_iff.mp wp).2 with aw|bw
    · exact ⟨w,v,aw,bv,p.reverse⟩
    exact ⟨v,w,av,bw,p⟩
  obtain ⟨aw,bw⟩ := (adjAll ws wh).1
  rcases (cut_mem_iff.mp vp).2 with av|bv
  · exact ⟨v,w,av,bw,p⟩
  exact ⟨w,v,aw,bv,p.reverse⟩

#print axioms terminal_mask_of_high_four_port_shore
#print axioms terminal_mask_of_very_small_four_port_shore
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
