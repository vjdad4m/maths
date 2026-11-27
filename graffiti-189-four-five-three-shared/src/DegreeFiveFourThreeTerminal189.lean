import UniversalRouteSingletons189
import WingSignature189
import DegreeFiveBothFiveResidual189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore from DegreeFiveActualCut189
open private anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private residue residue_count residual_neighbor_bound_nonport common_sub_ports from DegreeFiveBothFiveResidual189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- A four-port shore with three universal shared porters and at most
seven vertices has a terminal mask via a two-edge residual path. -/
theorem terminal_mask_at_four_ports_three_shared_short
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (four : (cutPorts C).card=4) (three : (sharedPortSet C).card=3)
    (small : (Shore C).card≤7)
    (univ : ∀ u∈sharedPortSet C,∀ v∈Shore C,u≠v → G.Adj u v) :
    WingRealizes G a b (Shore C) .terminal := by
  classical
  let K := sharedPortSet C
  let R := residue C
  have k3 : K.card=3 := three
  have sum : R.card+K.card=(Shore C).card := residue_count C
  have off : Disjoint K R := by
    apply disjoint_left.mpr
    intro w wk wr
    exact (mem_sdiff.mp wr).2 wk
  have whole : K∪R=Shore C := union_sdiff_of_subset (show K⊆Shore C from filter_subset _ _)
  have join (u : V) (uk : u∈K) (v : V) (vm : v∈K∪R) (ne : u≠v) : G.Adj u v :=
    univ u uk v (whole ▸ vm) ne
  obtain ⟨x,xk⟩ := card_pos.mp (show 0<K.card by omega)
  obtain ⟨_,ax,_⟩ := mem_filter.mp xk
  have pack {y : V} (yk : y∈K) (p : RouteOn G (K∪R) x y) :
      WingRealizes G a b (Shore C) .terminal :=
    ⟨x,y,ax,(mem_filter.mp yk).2.2,whole ▸ p⟩
  by_cases spare : R.card<K.card
  · obtain ⟨y,p,stop⟩ := universal_route_from_singletons K R xk off join (by omega)
    exact pack (stop spare) p
  let P := cutPorts C
  let W := Shore C\P
  have subset : P⊆Shore C := filter_subset _ _
  have w2 : 2≤W.card := by
    have h : W.card+P.card=(Shore C).card := card_sdiff_add_card_eq_card subset
    have c4 : P.card=4 := four
    omega
  obtain ⟨u,wm,uh⟩ := anywhere_high_of_two degree w2
  obtain ⟨us,up⟩ := mem_sdiff.mp wm
  have ur : u∈R := mem_sdiff.mpr ⟨us,fun h=>up (common_sub_ports C h)⟩
  have d := residual_neighbor_bound_nonport us up
  have p : 1<(R.filter (G.Adj u)).card := by
    change G.degree u≤K.card+(R.filter (G.Adj u)).card at d
    omega
  obtain ⟨v,vm,w,wm,vw⟩ := one_lt_card.mp p
  obtain ⟨vr,uv⟩ := mem_filter.mp vm
  obtain ⟨wr,uw⟩ := mem_filter.mp wm
  let Q : Finset V := {v,u,w}
  have sub : Q⊆R := insert_subset_iff.mpr ⟨vr,insert_subset_iff.mpr ⟨ur,singleton_subset_iff.mpr wr⟩⟩
  have card : Q.card=3 := by
    have no : v∉({u,w} : Finset V) := by simp [uv.ne.symm,vw]
    change (insert v ({u,w} : Finset V)).card=3
    rw [card_insert_of_not_mem no]
    simp [uw.ne]
  have tally := card_sdiff_add_card_eq_card sub
  obtain ⟨y,p,stop⟩ := universal_route_with_one_block K R Q xk
    (by simp [Q]) (by simp [Q]) off sub (RouteOn.three uv.symm uw vw) join (by omega)
  exact pack (stop (by omega)) p

#print axioms terminal_mask_at_four_universal_common_ports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
