import WingSignature189
import DegreeFiveBothFiveClique189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private cut_mem_iff common_sub_ports from DegreeFiveBothFiveResidual189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem free_mask_of_port_root
    {C : Cmp (G:=G) (a:=a) (b:=b)} {p q : V}
    (hp : p∈cutPorts C) (route : RouteOn G (Shore C) p q) :
    WingRealizes G a b (Shore C) .aFree ∨ WingRealizes G a b (Shore C) .bFree := by
  rcases (cut_mem_iff.mp hp).2 with ap|bp
  · exact .inl ⟨p,q,ap,route⟩
  exact .inr ⟨p,q,bp,route⟩

/-- Both saturated shores supply complementary original-graph masks.
The 5+5 parity budget guarantees a two-terminal wing; the other wing
can attach at at least one of the two original cuts. -/
theorem five_five_complementary_masks
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card  ≤  6)
    (degree : ∀ u v : V,u≠v → 5  ≤  G.degree u ∨ 5  ≤  G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (C5 : (cutPorts C).card=5) (D5 : (cutPorts D).card=5)
    {x y : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y) :
    ComplementaryWings G a b (Shore C) (Shore D) := by
  classical
  let K := sharedPortSet C
  let L := sharedPortSet D
  have xk : x∈K := mem_filter.mpr ⟨xc,ax,bx⟩
  have yk : y∈L := mem_filter.mpr ⟨yd,ay,by'⟩
  have cs : 5  ≤  (Shore C).card := by rw [←C5]; exact card_le_card (filter_subset _ _)
  have ds : 5  ≤  (Shore D).card := by rw [←D5]; exact card_le_card (filter_subset _ _)
  have k5 : K.card  ≤  5 := (card_le_card (common_sub_ports C)).trans (le_of_eq C5)
  have l5 : L.card  ≤  5 := (card_le_card (common_sub_ports D)).trans (le_of_eq D5)
  have uniC (u : V) (uk : u∈K) : ∀ w∈Shore C,u≠w → G.Adj u w := by
    obtain ⟨uc,au,bu⟩ := mem_filter.mp uk
    exact common_universal_in_shore_at_five hc even cd uc au bu D5
  have uniD (u : V) (uk : u∈L) : ∀ w∈Shore D,u≠w → G.Adj u w := by
    obtain ⟨ud,au,bu⟩ := mem_filter.mp uk
    exact common_universal_in_shore_at_five hc even cd.symm ud au bu C5
  obtain ⟨lim,wgt⟩ := both_five_shore_order_weighted hc two even cd xc ax bx yd ay by' C5 D5
  change 2*((Shore C).card+(Shore D).card)  ≤  18+K.card+L.card at wgt
  have cs9 : (Shore C).card ≤ 9 := by omega
  have ds9 : (Shore D).card ≤ 9 := by omega
  have Cterm (large : 3 ≤ K.card) (cap : (Shore C).card ≤ 2*K.card) :
      WingRealizes G a b (Shore C) .terminal := by
    obtain ⟨u,p,stop⟩ := rooted_route_at_five_port_shore_with_big_shared degree C5 large cs9
      (by change (Shore C).card ≤ 2*K.card+2; omega) xk uniC
    exact ⟨x,u,ax,(mem_filter.mp (stop cap)).2.2,p⟩
  have Dterm (large : 3 ≤ L.card) (cap : (Shore D).card ≤ 2*L.card) :
      WingRealizes G a b (Shore D) .terminal := by
    obtain ⟨v,p,stop⟩ := rooted_route_at_five_port_shore_with_big_shared degree D5 large ds9
      (by change (Shore D).card ≤ 2*L.card+2; omega) yk uniD
    exact ⟨y,v,ay,(mem_filter.mp (stop cap)).2.2,p⟩
  by_cases big : 3 ≤ K.card ∧ 3 ≤ L.card
  · have roomC : (Shore C).card ≤ 2*K.card+2 := by omega
    have roomD : (Shore D).card ≤ 2*L.card+2 := by omega
    obtain ⟨u,p,_⟩ := rooted_route_at_five_port_shore_with_big_shared degree C5 big.1 cs9 roomC xk uniC
    obtain ⟨v,q,_⟩ := rooted_route_at_five_port_shore_with_big_shared degree D5 big.2 ds9 roomD yk uniD
    by_cases ok : (Shore C).card ≤ 2*K.card
    · exact .inl ⟨Cterm big.1 ok,.inl ⟨y,v,ay,q⟩⟩
    have other : (Shore D).card ≤ 2*L.card := by omega
    exact .inr ⟨Dterm big.2 other,.inl ⟨x,u,ax,p⟩⟩
  have small : (Shore C).card+(Shore D).card ≤ 12 := by
    by_cases h : 3 ≤ K.card
    · have no : L.card<3 := Nat.lt_of_not_ge (fun t=>big ⟨h,t⟩)
      omega
    omega
  obtain ⟨r,rp,u,p⟩ := rooted_port_route_at_small_five_shore degree C5 (by omega) xk uniC
  obtain ⟨s,sp,v,q⟩ := rooted_port_route_at_small_five_shore degree D5 (by omega) yk uniD
  have rmask := free_mask_of_port_root rp p
  have smask := free_mask_of_port_root sp q
  by_cases c5 : (Shore C).card=5
  · exact .inl ⟨terminal_route_at_five_vertex_all_port_shore degree C5 c5 xk uniC,smask⟩
  by_cases d5 : (Shore D).card=5
  · exact .inr ⟨terminal_route_at_five_vertex_all_port_shore degree D5 d5 yk uniD,rmask⟩
  by_cases ck : 3 ≤ K.card
  · exact .inl ⟨Cterm ck (by omega),smask⟩
  have dk : 3 ≤ L.card := by omega
  exact .inr ⟨Dterm dk (by omega),rmask⟩

#print axioms five_five_complementary_masks
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
