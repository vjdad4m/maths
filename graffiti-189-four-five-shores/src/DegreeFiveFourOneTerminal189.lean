import DegreeFiveUniversalNonisolated189
import ResidualConnectivity189
import RootedOreExceptPair189
import WingSignature189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset ArticulationPair
open private Shore from DegreeFiveActualCut189
open private anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private sharedPortSet inside_high_at_least_four_if_exclusive from DegreeFiveBalancedCommonRoot189
open private cut_mem_iff common_sub_ports residue residue_count residual_neighbor_bound from DegreeFiveBothFiveResidual189
open private lift_side_path from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

/-- With one universal common porter, three actual exclusive contact
choices permit Ore to root the residual route and preserve a terminal. -/
theorem terminal_four_port_one_common_at_most_six
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (four : (cutPorts C).card=4) (one : (sharedPortSet C).card=1)
    (small : (Shore C).card≤6)
    {x y : V} (xK : x∈sharedPortSet C)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y)
    (univ : ∀ w∈Shore C,x≠w → G.Adj x w) :
    WingRealizes G a b (Shore C) .terminal := by
  classical
  let S := Shore C
  let K := sharedPortSet C
  let P := cutPorts C
  let R := residue C
  let E := P\K
  have k1 : K.card=1 := one
  have p4 : P.card=4 := four
  have e3 : E.card=3 := by
    have q : E.card+K.card=P.card := card_sdiff_add_card_eq_card (common_sub_ports C)
    omega
  have sum : R.card+K.card=S.card := residue_count C
  have eSub : E⊆R := by
    intro z ze
    obtain ⟨zp,zn⟩ := mem_sdiff.mp ze
    exact mem_sdiff.mpr ⟨(cut_mem_iff.mp zp).1,zn⟩
  have lower : 5≤S.card := by
    obtain ⟨z,ze,z5⟩ := anywhere_high_of_two degree (show 2≤E.card by omega)
    obtain ⟨zp,zn⟩ := mem_sdiff.mp ze
    have zs := (cut_mem_iff.mp zp).1
    have zOff : ¬(G.Adj a z ∧ G.Adj b z) := fun h=>zn (mem_filter.mpr ⟨zs,h⟩)
    have p := inside_high_at_least_four_if_exclusive zs z5 zOff
    have sub : inside G S z⊆S.erase z := by
      intro w wm
      obtain ⟨ws,zw⟩ := mem_filter.mp wm
      exact mem_erase.mpr ⟨zw.ne.symm,ws⟩
    have c := card_le_card sub
    rw [card_erase_of_mem (show z∈S from zs)] at c
    change 4≤(inside G S z).card at p
    omega
  have noIso := one_common_residue_nonisolated_at_order_ge_five hc two even degree cd lower
    one xK yd ay by' univ
  let U := ↑(↑R : Set V)
  let J := G.induce (↑R : Set V)
  let A : Finset U := Finset.univ.filter (fun u=>u.val∈E)
  have app (u : U) : u∈A ↔ u.val∈E := by simp [A]
  have hA : A.card=E.card := by
    apply card_bij (fun u _=>u.val)
    · intro u hm
      exact (app u).mp hm
    · intro u _ v _ e
      exact Subtype.ext e
    intro v ve
    exact ⟨⟨v,eSub ve⟩,(app ⟨v,eSub ve⟩).mpr ve,rfl⟩
  have n : Fintype.card U=R.card := Fintype.card_coe R
  have upper : R.card≤5 := by
    have q : S.card≤6 := small
    omega
  have indeg (u : U) : (R.filter (G.Adj u.val)).card=J.degree u :=
    inside_card_eq_degree_induce (G:=G) R u
  have pair (u v : U) (uv : u≠v) : 3≤J.degree u ∨ 3≤J.degree v := by
    have aU : G.degree u.val≤K.card+(R.filter (G.Adj u.val)).card+1 := residual_neighbor_bound u.property
    have aV : G.degree v.val≤K.card+(R.filter (G.Adj v.val)).card+1 := residual_neighbor_bound v.property
    rw [indeg u] at aU
    rw [indeg v] at aV
    exact (degree u.val v.val (fun e=>uv (Subtype.ext e))).imp
      (fun h=>by omega) (fun h=>by omega)
  have hp : Nonempty U := by
    obtain ⟨z,ze⟩ := card_pos.mp (show 0<E.card by omega)
    exact ⟨⟨z,eSub ze⟩⟩
  have con : J.Connected := connected_of_pair_degree_and_no_isolates 3 hp (by change Fintype.card U ≤ 2*3+1; omega) pair
    (fun u=>by obtain ⟨v,vr,uv⟩ := noIso u.val u.property; exact ⟨⟨v,vr⟩,uv⟩)
  have cap (u v : U) (hu : 3≤J.degree u) (hv : 3≤J.degree v) (_ : u≠v)
      (_ : ¬(u∈(∅ : Finset U) ∧ v∈(∅ : Finset U))) : Fintype.card U≤J.degree u+J.degree v := by omega
  obtain ⟨r,ra,t,p,pp,ps⟩ := rooted_Ore_except_pair con A ∅ (by omega)
    (by simp) (.inl (by simp)) (fun u=>3≤J.degree u) pair cap
  have route : RouteOn G R r.val t.val := lift_side_path R p pp ps
  have tS := (mem_sdiff.mp t.property).1
  have xR : x∉R := fun h=>(mem_sdiff.mp h).2 xK
  have xt := univ t.val tS (fun h=>xR (h.symm ▸ t.property))
  have keq : K={x} := by
    have xk : x∈K := xK
    exact (eq_of_subset_of_card_le (singleton_subset_iff.mpr xk) (by simp [k1])).symm
  have eq : insert x R=Shore C := by
    have h : K∪R=Shore C := union_sdiff_of_subset (show K⊆Shore C from filter_subset _ _)
    rw [←h,keq]
    ext w
    simp
  have full : RouteOn G (Shore C) r.val x := eq ▸ route.suffix xt.symm xR
  have rp := (mem_sdiff.mp ((app r).mp ra)).1
  obtain ⟨_,ax,bx⟩ := mem_filter.mp xK
  rcases (cut_mem_iff.mp rp).2 with ar|br
  · exact ⟨r.val,x,ar,bx,full⟩
  exact ⟨x,r.val,ax,br,full.reverse⟩

#print axioms terminal_four_port_one_common_at_most_six
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
