import DegreeFiveFourFiveThreeShared189
import DegreeFiveFourOneTerminal189
import DegreeFiveFourTwoTerminal189
import DegreeFiveNearAllPortTerminal189
import ResidualOreParam189
import RootedTwoUniversal189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore shore_off shore_closed shore_disjoint shore_connected shore_hit_a shore_hit_b
  from DegreeFiveActualCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private cut_mem_iff residue residue_count residual_neighbor_bound from DegreeFiveBothFiveResidual189
open private shores_add_two_le_graph_order from DegreeFiveBothFourFiveFifteenClose189




variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- All both-common (4,5) cuts have complementary spanning wing signatures. -/
theorem four_five_both_common_masks
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C4 : (cutPorts C).card=4) (D5 : (cutPorts D).card=5)
    {x y : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y) :
    ComplementaryWings G a b (Shore C) (Shore D) := by

  classical
  have cLower : 4≤(cutPorts C).card := by omega
  have dLower : 4≤(cutPorts D).card := by omega
  by_cases shared : 3≤(sharedPortSet C).card
  · exact four_five_at_least_three_shared_masks hc two even conn degree cd cover C4 D5 shared xc ax bx yd ay by'
  have xK : x∈sharedPortSet C := mem_filter.mpr ⟨xc,ax,bx⟩
  have kpos : 0<(sharedPortSet C).card := card_pos.mpr ⟨x,xK⟩
  have nUpper := both_common_nonsaturated_order_le_fifteen hc two even conn cd cover
    cLower dLower (.inl C4) xc ax bx yd ay by'
  by_cases n15 : Fintype.card V=15
  · obtain ⟨term,free,_⟩ := four_five_order_fifteen_masks hc two even conn degree cd cover
      C4 D5 n15 xc ax bx yd ay by'
    exact .inl ⟨term,.inl free⟩
  have ab : a≠b := by intro e; rw [e,SimpleGraph.dist_self] at two; omega
  have sum := shores_add_two_le_graph_order ab cd
  have c4 : 4≤(Shore C).card := by rw [←C4]; exact card_le_card (filter_subset _ _)
  have d5 : 5≤(Shore D).card := by rw [←D5]; exact card_le_card (filter_subset _ _)
  have cUniv (u : V) (uk : u∈sharedPortSet C) : ∀ w∈Shore C,u≠w → G.Adj u w := by
    obtain ⟨uc,au,bu⟩ := mem_filter.mp uk
    exact common_universal_in_shore_at_five hc even cd uc au bu D5
  have cross {u v : V} (uc : u∈Shore C) (vd : v∈Shore D) : ¬G.Adj u v := by
    intro e
    rcases shore_closed C u uc v e with rfl|rfl|vC
    · exact (shore_off D).1 vd
    · exact (shore_off D).2 vd
    exact disjoint_left.mp (shore_disjoint cd) vC vd
  let T : Split G a b := ⟨Shore D,Shore C,shore_disjoint cd.symm,shore_off D,shore_off C,
    shore_connected D,(fun _ vd _ uc e=>cross uc vd e.symm),shore_hit_a ab conn D,shore_hit_b ab conn D,
    (fun z=>(cover z).imp id (fun h=>h.imp id Or.symm))⟩
  have near (u : V) (uk : u∈sharedPortSet D) :
      (secondShore D u).card≤1 ∧ ∀ w∈Shore D,G.dist u w≤2 := by
    obtain ⟨ud,au,bu⟩ := mem_filter.mp uk
    exact Split.Five.near_universal_at_four_foreign T hc even conn ud au bu cLower
  by_cases small : (Shore C).card≤6
  · have term : WingRealizes G a b (Shore C) .terminal := by
      by_cases k1 : (sharedPortSet C).card=1
      · exact terminal_four_port_one_common_at_most_six hc two even degree cd C4 k1 small xK yd ay by' (cUniv x xK)
      have k2 : (sharedPortSet C).card=2 := by omega
      exact terminal_four_port_two_common_at_most_six degree C C4 k2 small cUniv
    obtain ⟨r,rp,t,path⟩ := port_rooted_of_near_shore_at_most_eight hc degree d5 (by omega)
      (by omega) near
    rcases (cut_mem_iff.mp rp).2 with ar|br
    · exact .inl ⟨term,.inl ⟨r,t,ar,path⟩⟩
    exact .inl ⟨term,.inr ⟨r,t,br,path⟩⟩
  have c7 : (Shore C).card=7 := by omega
  have dExact : (Shore D).card=5 := by omega
  have term := terminal_mask_of_five_vertex_all_port_shore degree D5 dExact yd ay by'
  apply Or.inr
  refine ⟨term,Or.inl ?_⟩
  let K := sharedPortSet C
  let R := residue C
  have split : K∪R=Shore C := union_sdiff_of_subset (filter_subset _ _)
  have counts : R.card+K.card=7 := (residue_count C).trans c7
  have apart : Disjoint K R := disjoint_sdiff_self_right
  have join (u : V) (uk : u∈K) (w : V) (wh : w∈K∪R) (uw : u≠w) : G.Adj u w :=
    cUniv u uk w (split ▸ wh) uw
  have kPos : 0<K.card := kpos
  have kUpper : K.card<3 := Nat.lt_of_not_ge shared
  have pair (u : V) (ur : u∈R) (v : V) (vr : v∈R) (uv : u≠v) :
      4-K.card≤(R.filter (G.Adj u)).card ∨ 4-K.card≤(R.filter (G.Adj v)).card := by
    have p : G.degree u≤K.card+(R.filter (G.Adj u)).card+1 := residual_neighbor_bound ur
    have q : G.degree v≤K.card+(R.filter (G.Adj v)).card+1 := residual_neighbor_bound vr
    exact (degree u v uv).imp (fun h=>by omega) (fun h=>by omega)
  by_cases k1 : K.card=1
  · have noIso := one_common_residue_nonisolated_at_order_ge_five hc two even degree cd
      (show 5≤(Shore C).card by omega) k1 xK yd ay by' (cUniv x xK)
    have pos : R.Nonempty := card_pos.mp (show 0<R.card by omega)
    obtain ⟨v,vr,w,wr,p⟩ := residual_route_if_low_not_isolated_at_d 3 R (by omega)
      pos (fun u hu v hv uv=>by simpa [k1] using pair u hu v hv uv) (fun u hu _=>noIso u hu)
    have xv := cUniv x xK v (mem_sdiff.mp vr).1 (fun e=>(mem_sdiff.mp vr).2 (e ▸ xK))
    have no : x∉R := fun h=>(mem_sdiff.mp h).2 xK
    have keq : K={x} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr xK) (by change K.card≤1; omega)).symm
    have all : insert x R=Shore C := by simpa [keq] using split
    exact ⟨x,w,ax,all ▸ p.prefix xv no⟩
  have k2 : K.card=2 := by omega
  obtain ⟨w,p⟩ := rooted_route_with_two_universal K R k2 (by omega) xK apart join
    (fun u hu v hv uv=>by simpa [k2] using pair u hu v hv uv)
  exact ⟨x,w,ax,split ▸ p⟩

#print axioms four_five_both_common_masks
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
