import DegreeFiveBothFiveResidual189
import UniversalRouteSingletons189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private residue residue_count common_sub_ports from DegreeFiveBothFiveResidual189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- The common-clique and residual-block route. If the split has enough
common vertices relative to the residue, the other endpoint is common. -/
theorem rooted_route_at_five_port_shore_with_big_shared
    (degree : ∀ u v : V,u≠v → 5 ≤ G.degree u ∨ 5 ≤ G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (five : (cutPorts C).card=5)
    (shared : 3 ≤ (sharedPortSet C).card)
    (small : (Shore C).card ≤ 9)
    (room : (Shore C).card ≤ 2*(sharedPortSet C).card+2)
    {x : V} (xK : x∈sharedPortSet C)
    (univ : ∀ u∈sharedPortSet C,∀ w∈Shore C,u≠w → G.Adj u w) :
    ∃ y,RouteOn G (Shore C) x y ∧
      ((Shore C).card ≤ 2*(sharedPortSet C).card → y∈sharedPortSet C) := by
  classical
  let K := sharedPortSet C
  let R := residue C
  have tally : R.card+K.card=(Shore C).card := residue_count C
  have k3 : 3 ≤ K.card := shared
  have maxK : K.card ≤ 5 := (card_le_card (common_sub_ports C)).trans (le_of_eq five)
  have off : Disjoint K R := by
    apply disjoint_left.mpr
    intro w wk wr
    exact (mem_sdiff.mp wr).2 wk
  have whole : K∪R=Shore C := union_sdiff_of_subset (show K⊆Shore C from filter_subset _ _)
  have join (u : V) (uk : u∈K) (w : V) (wm : w∈K∪R) (uw : u≠w) : G.Adj u w :=
    univ u uk w (whole ▸ wm) uw
  have finish {y : V} (p : RouteOn G (K∪R) x y) (t : R.card≤K.card → y∈K) :
      RouteOn G (Shore C) x y ∧
      ((Shore C).card≤2*(sharedPortSet C).card → y∈sharedPortSet C) := by
    refine ⟨whole ▸ p,?_⟩
    intro h
    have h' : (Shore C).card≤2*K.card := h
    exact t (by omega)
  by_cases basic : R.card<K.card
  · obtain ⟨y,p,stop⟩ := universal_route_from_singletons K R xK off join (by omega)
    exact ⟨y,finish p (fun _=>stop basic)⟩
  have split : R.card≤K.card+2 := by
    have h : (Shore C).card≤2*K.card+2 := room
    omega
  by_cases better : R.card≤K.card+1
  · have cond : (sharedPortSet C).card=3 ∨
        ((sharedPortSet C).card=4 ∧ 7≤(Shore C).card) := by
      change K.card=3 ∨ (K.card=4 ∧ 7≤(Shore C).card)
      omega
    obtain ⟨u,ur,v,vr,uv⟩ := residual_edge_at_five_with_big_shared degree five cond
    let P : Finset V := {u,v}
    have pr : P⊆R := by simpa [P] using (show ({u,v} : Finset V)⊆R from
      (insert_subset_iff.mpr ⟨ur,singleton_subset_iff.mpr vr⟩))
    have p2 : P.card=2 := by simp [P,uv.ne]
    have eq := card_sdiff_add_card_eq_card pr
    obtain ⟨y,p,stop⟩ := universal_route_with_one_block K R P xK
      (by simp [P]) (by simp [P]) off pr (RouteOn.edge uv) join (by omega)
    exact ⟨y,finish p (fun m=>stop (by omega))⟩
  have kk : (sharedPortSet C).card=3 := by change K.card=3; omega
  have big : 7≤(Shore C).card := by omega
  obtain ⟨u,ur,v,vr,w,wr,uw,uv,vw⟩ := residual_two_edges_at_five_with_three_shared degree five kk big
  let P : Finset V := {u,v,w}
  have pr : P⊆R := insert_subset_iff.mpr ⟨ur,insert_subset_iff.mpr ⟨vr,singleton_subset_iff.mpr wr⟩⟩
  have p3 : P.card=3 := by
    have h : u∉({v,w} : Finset V) := by simp [uv.ne,uw]
    change (insert u ({v,w} : Finset V)).card=3
    rw [card_insert_of_not_mem h]
    simp [vw.ne]
  have eq := card_sdiff_add_card_eq_card pr
  obtain ⟨y,p,_⟩ := universal_route_with_one_block K R P xK
    (by simp [P]) (by simp [P]) off pr (RouteOn.three uv vw uw) join (by omega)
  exact ⟨y,finish p (fun h=>by omega)⟩

#print axioms rooted_route_at_five_port_shore_with_big_shared
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
