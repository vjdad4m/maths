import DegreeFiveBothFiveNonisolated189
import DegreeFiveBothFiveMasks189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private residue residue_count residual_neighbor_bound common_sub_ports
  from DegreeFiveBothFiveResidual189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- In the saturated both-common setting, each specified common
porter can root a spanning path of its own shore. -/
theorem common_rooted_at_both_five
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (degree : ∀ u v : V,u≠v → 5 ≤ G.degree u ∨ 5 ≤ G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (C5 : (cutPorts C).card=5) (D5 : (cutPorts D).card=5)
    {x y : V} (xK : x∈sharedPortSet C)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y) :
    ∃ v,RouteOn G (Shore C) x v := by
  classical
  let K := sharedPortSet C
  let R := residue C
  obtain ⟨xc,ax,bx⟩ := mem_filter.mp xK
  obtain ⟨lim,wgt⟩ := both_five_shore_order_weighted hc two even cd xc ax bx yd ay by' C5 D5
  change 2*((Shore C).card+(Shore D).card) ≤ 18+K.card+(sharedPortSet D).card at wgt
  have tally : R.card+K.card=(Shore C).card := residue_count C
  have Kpos := card_pos.mpr ⟨x,show x∈K from xK⟩
  have maxD : (sharedPortSet D).card ≤ 5 := (card_le_card (common_sub_ports D)).trans (le_of_eq D5)
  have cs : 5 ≤ (Shore C).card := by rw [←C5]; exact card_le_card (filter_subset _ _)
  have ds : 5 ≤ (Shore D).card := by rw [←D5]; exact card_le_card (filter_subset _ _)
  have univ (z : V) (zk : z∈K) : ∀ w∈Shore C,z≠w → G.Adj z w := by
    obtain ⟨zc,az,bz⟩ := mem_filter.mp zk
    exact common_universal_in_shore_at_five hc even cd zc az bz D5
  by_cases large : 3 ≤ K.card
  · have room : (Shore C).card ≤ 2*K.card+2 := by omega
    obtain ⟨v,p,_⟩ := rooted_route_at_five_port_shore_with_big_shared degree C5 large (by omega)
      room xK univ
    exact ⟨v,p⟩
  have off : Disjoint K R := by
    apply disjoint_left.mpr
    intro w wk wr
    exact (mem_sdiff.mp wr).2 wk
  have whole : K∪R=Shore C := union_sdiff_of_subset (show K⊆Shore C from filter_subset _ _)
  have join (z : V) (zk : z∈K) (w : V) (wm : w∈K∪R) (zw : z≠w) : G.Adj z w :=
    univ z zk w (whole ▸ wm) zw
  by_cases k2 : K.card=2
  · have pair (u : V) (ur : u∈R) (v : V) (vr : v∈R) (uv : u≠v) :
        2 ≤ (R.filter (G.Adj u)).card ∨ 2 ≤ (R.filter (G.Adj v)).card := by
      have p : G.degree u ≤ K.card+(R.filter (G.Adj u)).card+1 := residual_neighbor_bound ur
      have q : G.degree v ≤ K.card+(R.filter (G.Adj v)).card+1 := residual_neighbor_bound vr
      exact (degree u v uv).imp (fun h=>by omega) (fun h=>by omega)
    obtain ⟨v,p⟩ := rooted_route_with_two_universal K R k2 (by omega) xK off join pair
    exact ⟨v,whole ▸ p⟩
  have k1 : K.card=1 := by omega
  have xm : x∈K := xK
  have eq : K={x} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr xm)
    (by simp [k1])).symm
  have pos : R.Nonempty := card_pos.mp (by omega)
  have pair (u : V) (ur : u∈R) (v : V) (vr : v∈R) (uv : u≠v) :
      3 ≤ (R.filter (G.Adj u)).card ∨ 3 ≤ (R.filter (G.Adj v)).card := by
    have p : G.degree u ≤ K.card+(R.filter (G.Adj u)).card+1 := residual_neighbor_bound ur
    have q : G.degree v ≤ K.card+(R.filter (G.Adj v)).card+1 := residual_neighbor_bound vr
    exact (degree u v uv).imp (fun h=>by omega) (fun h=>by omega)
  have nonisolated := one_common_residue_nonisolated_at_five hc two even degree cd C5 k1
    xK yd ay by' (univ x xK)
  obtain ⟨u,ur,v,vr,p⟩ := residual_route_if_low_not_isolated R (by omega) pos pair
    (fun w wr _=>nonisolated w wr)
  have xr : x∉R := fun h=>disjoint_left.mp off xK h
  have xu : G.Adj x u := join x xK u (mem_union_right _ ur) (fun e=>xr (e.symm ▸ ur))
  have f : insert x R=Shore C := by rw [←whole,eq]; ext z; simp
  exact ⟨v,f ▸ p.prefix xu xr⟩

/-- Thus both free masks are available on each shore, and at least
one of the two shores also realizes the two-terminal mask. -/
theorem five_five_free_masks_and_terminal
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (degree : ∀ u v : V,u≠v → 5 ≤ G.degree u ∨ 5 ≤ G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (C5 : (cutPorts C).card=5) (D5 : (cutPorts D).card=5)
    {x y : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y) :
    WingRealizes G a b (Shore C) .aFree ∧ WingRealizes G a b (Shore C) .bFree ∧
    WingRealizes G a b (Shore D) .aFree ∧ WingRealizes G a b (Shore D) .bFree ∧
    (WingRealizes G a b (Shore C) .terminal ∨ WingRealizes G a b (Shore D) .terminal) := by
  have xk : x∈sharedPortSet C := mem_filter.mpr ⟨xc,ax,bx⟩
  have yk : y∈sharedPortSet D := mem_filter.mpr ⟨yd,ay,by'⟩
  obtain ⟨u,p⟩ := common_rooted_at_both_five hc two even degree cd C5 D5 xk yd ay by'
  obtain ⟨v,q⟩ := common_rooted_at_both_five hc two even degree cd.symm D5 C5 yk xc ax bx
  have full := five_five_complementary_masks hc two even degree cd C5 D5 xc ax bx yd ay by'
  exact ⟨⟨x,u,ax,p⟩,⟨x,u,bx,p⟩,⟨y,v,ay,q⟩,⟨y,v,by',q⟩,
    full.imp And.left And.left⟩

#print axioms common_rooted_at_both_five
#print axioms five_five_free_masks_and_terminal
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
