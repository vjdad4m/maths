import DegreeFiveOneFiveFarProfile189
import DegreeFiveThreeFourClose189



namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint shore_nonempty shore_connected shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
open private secondShore from DegreeFiveDistanceTwoThreeClose189
open private Cmp two_shore_budget count_cut_degree_on_two_shores portColor from DegreeFiveThreeForeignImpossible189
open private four_in_nonsingleton second_positive_of_small_ports anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private nonport_neighbors_subset nonport_degree_bound_small from DegreeFiveThreeFiveShapes189
open private nonport_mem_second_iff_neighbor_port from DegreeFiveOneFiveFarProfile189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem boundary_has_at_least_two
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {Q W : Finset V} (interior : ∃ x∈Q,x∉W) {y : V} (yQ : y∉Q) (yW : y∉W)
    (step : ∀ x∈Q,∀ z,z∉Q → G.Adj x z → x∈W ∨ z∈W) :
    2≤W.card := by
  classical
  apply Classical.byContradiction
  intro n
  obtain ⟨x,xq,xw⟩ := interior
  let U := ((↑W : Set V)ᶜ)
  let J := G.induce U
  let xx : U := ⟨x,xw⟩
  let yy : U := ⟨y,yW⟩
  have walk_on {u v : U} (p : J.Walk u v) : u.val∈Q → v.val∈Q := by
    induction p with
    | nil => exact id
    | @cons u w v e p ih =>
      intro uq
      apply ih
      apply Classical.byContradiction
      intro nw
      exact (step u.val uq w.val nw e).elim u.property w.property
  obtain ⟨p⟩ := (conn W (by omega)).preconnected xx yy
  exact yQ (walk_on p xq)

private theorem two_port_shore_size_at_least_six
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp (G:=G) (a:=a) (b:=b)} (two : (cutPorts C).card=2) :
    6≤(Shore C).card := by
  classical
  let F := Shore C\cutPorts C
  have cover : F.card+(cutPorts C).card=(Shore C).card :=
    card_sdiff_add_card_eq_card (filter_subset _ _)
  have bound : (cutPorts C).card≤(Shore C).card := card_le_card (filter_subset _ _)
  have four := four_in_nonsingleton degree (show 2≤(Shore C).card by omega)
  apply Classical.byContradiction
  intro h
  obtain ⟨u,uf,v,vf,uv⟩ := one_lt_card.mp (show 1<F.card by omega)
  obtain ⟨uc,un⟩ := mem_sdiff.mp uf
  obtain ⟨vc,vn⟩ := mem_sdiff.mp vf
  have p := nonport_degree_bound_small uc un
  have q := nonport_degree_bound_small vc vn
  exact (degree u v uv).elim (fun h=>by omega) (fun h=>by omega)

private theorem cut_a_touches_all_at_two_three
    (two : G.dist a b=2)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C2 : (cutPorts C).card=2) (D3 : (cutPorts D).card=3)
    (high : 5≤G.degree a) :
    (∀ z∈cutPorts C,G.Adj a z) ∧ (∀ z∈cutPorts D,G.Adj a z) := by
  classical
  have tally := count_cut_degree_on_two_shores cd cover two (.inl rfl : a=a ∨ a=b)
  have sub (K : Cmp (G:=G) (a:=a) (b:=b)) : portColor K a⊆cutPorts K := by
    intro z h
    obtain ⟨zc,az⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨zc,.inl az⟩
  have c := card_le_card (sub C)
  have d := card_le_card (sub D)
  have ce : portColor C a=cutPorts C := eq_of_subset_of_card_le (sub C) (by omega)
  have de : portColor D a=cutPorts D := eq_of_subset_of_card_le (sub D) (by omega)
  exact ⟨fun z h=>(mem_filter.mp (ce.symm ▸ h)).2,fun z h=>(mem_filter.mp (de.symm ▸ h)).2⟩

/-- With the first cut touching all ports, these are precisely the visible
and dark nonporters of a shore. -/
private noncomputable def dark (C : Cmp (G:=G) (a:=a) (b:=b)) : Finset V :=
  (Shore C\cutPorts C)\secondShore C a

private theorem visible_in_nonports
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (all : ∀ z∈cutPorts C,G.Adj a z) :
    secondShore C a⊆Shore C\cutPorts C := by
  intro z h
  have z2 : G.dist a z=2 := by simpa [DistanceTwo] using (mem_inter.mp h).2
  exact mem_sdiff.mpr ⟨(mem_inter.mp h).1,fun e=>by
    have h := dist_eq_one_iff_adj.mpr (all z e)
    omega⟩

private theorem dark_boundary_is_visible
    (hc : G.Connected) {C : Cmp (G:=G) (a:=a) (b:=b)}
    (all : ∀ z∈cutPorts C,G.Adj a z) {x z : V}
    (xd : x∈dark C) (xz : G.Adj x z) (no : z∉dark C) :
    z∈secondShore C a := by
  obtain ⟨h,xOff⟩ := mem_sdiff.mp xd
  obtain ⟨xC,xP⟩ := mem_sdiff.mp h
  rcases shore_closed C x xC z xz with h|h|zc
  · exact (xP (mem_filter.mpr ⟨xC,.inl (h ▸ xz.symm)⟩)).elim
  · exact (xP (mem_filter.mpr ⟨xC,.inr (h ▸ xz.symm)⟩)).elim
  by_cases zP : z∈cutPorts C
  · have k : z∈portColor C a := mem_filter.mpr ⟨zc,all z zP⟩
    exact (xOff ((nonport_mem_second_iff_neighbor_port hc xC xP (.inl rfl)).mpr ⟨z,k,xz⟩)).elim
  exact Classical.byContradiction (fun h=>no (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨zc,zP⟩,h⟩))

private theorem visible_at_least_two_of_dark
    (hc : G.Connected)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    {C : Cmp (G:=G) (a:=a) (b:=b)}
    (all : ∀ z∈cutPorts C,G.Adj a z) (nonempty : (dark C).Nonempty) :
    2≤(secondShore C a).card := by
  obtain ⟨x,xd⟩ := nonempty
  have notA : a∉Shore C := (shore_off C).1
  have no : a∉dark C := fun h=>notA (mem_sdiff.mp (mem_sdiff.mp h).1).1
  have na : a∉secondShore C a := fun h=>notA (mem_inter.mp h).1
  refine boundary_has_at_least_two conn ⟨x,xd,(mem_sdiff.mp xd).2⟩ no na ?_
  intro u ud w wo uw
  exact .inr (dark_boundary_is_visible hc all ud uw wo)

#print axioms boundary_has_at_least_two
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
