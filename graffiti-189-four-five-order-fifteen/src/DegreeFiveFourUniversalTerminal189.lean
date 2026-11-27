import UniversalRouteSingletons189
import WingSignature189
import DegreeFiveBothFiveResidual189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private Shore from DegreeFiveActualCut189
open private anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet from DegreeFiveBalancedCommonRoot189
open private residue residue_count residual_neighbor_bound_nonport from DegreeFiveBothFiveResidual189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- Four common universal porters supply both cut endpoints, even
when an eight-vertex shore requires one nontrivial residual block. -/
theorem terminal_mask_at_four_universal_common_ports
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (four : (cutPorts C).card=4) (pure : sharedPortSet C=cutPorts C)
    (small : (Shore C).card≤8)
    (univ : ∀ u∈sharedPortSet C,∀ v∈Shore C,u≠v → G.Adj u v) :
    WingRealizes G a b (Shore C) .terminal := by
  classical
  let K := sharedPortSet C
  let R := residue C
  have k4 : K.card=4 := by change (sharedPortSet C).card=4; rw [pure,four]
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
  obtain ⟨u,ur,uh⟩ := anywhere_high_of_two degree (show 2≤R.card by omega)
  obtain ⟨us,uk⟩ := mem_sdiff.mp ur
  have up : u∉cutPorts C := fun h=>uk (pure.symm ▸ h)
  have d := residual_neighbor_bound_nonport us up
  have p : 0<(R.filter (G.Adj u)).card := by
    change G.degree u≤K.card+(R.filter (G.Adj u)).card at d
    omega
  obtain ⟨v,vm⟩ := card_pos.mp p
  obtain ⟨vr,uv⟩ := mem_filter.mp vm
  let P : Finset V := {u,v}
  have sub : P⊆R := insert_subset_iff.mpr ⟨ur,singleton_subset_iff.mpr vr⟩
  have card : P.card=2 := by simp [P,uv.ne]
  have tally := card_sdiff_add_card_eq_card sub
  obtain ⟨y,p,stop⟩ := universal_route_with_one_block K R P xk
    (by simp [P]) (by simp [P]) off sub (RouteOn.edge uv) join (by omega)
  exact pack (stop (by omega)) p

#print axioms terminal_mask_at_four_universal_common_ports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
