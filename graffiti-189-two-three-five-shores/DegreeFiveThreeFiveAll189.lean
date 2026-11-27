import DegreeFiveThreeFiveTerminal189
import DegreeFiveThreeFiveFree189
import DegreeFiveThreeFiveSeven189
import DegreeFiveNearAllPortTerminal189
import DegreeFiveBothFourFiveFifteenClose189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private shores_add_two_le_graph_order from DegreeFiveBothFourFiveFifteenClose189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem pair_deletion_min_degree_two
    (order : 3≤Fintype.card V)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected) :
    ∀ z : V,2≤G.degree z := by
  classical
  intro z
  apply Classical.byContradiction
  intro fail
  let R := G.neighborFinset z
  have card : R.card=G.degree z := card_neighborFinset_eq_degree G z
  have hn : R.card<2 := by omega
  let S := (univ \ R).erase z
  have diff := card_sdiff_add_card_eq_card (show R⊆univ from subset_univ _)
  have un : (univ : Finset V).card=Fintype.card V := card_univ
  have inZ : z∈(univ \ R) := by simp [R]
  have sN : 0<S.card := by
    change 0<((univ \ R).erase z).card
    rw [card_erase_of_mem inZ]
    omega
  obtain ⟨w,wm⟩ := card_pos.mp sN
  obtain ⟨wz,wr⟩ := mem_erase.mp wm
  let U := ((↑R : Set V)ᶜ)
  let J := G.induce U
  let zz : U := ⟨z,by simpa using (mem_sdiff.mp inZ).2⟩
  let ww : U := ⟨w,by simpa using (mem_sdiff.mp wr).2⟩
  obtain ⟨p⟩ := (conn R hn).preconnected zz ww
  have noPath {x y : U} (p : J.Walk x y) (root : x.val=z) : y.val=z := by
    cases p with
    | nil => exact root
    | @cons x y t e p =>
      have g : G.Adj z y.val := root ▸ (show G.Adj x.val y.val from e)
      exact (y.property ((mem_neighborFinset G z y.val).mpr g)).elim
  exact wz (noPath p rfl)

theorem traceable_of_actual_five_three_five_ports
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C3 : (cutPorts C).card=3) (D5 : (cutPorts D).card=5)
    {x y : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (yd : y∈Shore D) (ay : G.Adj a y) (by' : G.Adj b y) :
    ∃ r t : V,∃ q : G.Walk r t,q.IsPath ∧ ∀ p,p∈q.support := by
  classical
  have ab : a≠b := by intro e; rw [e,dist_self] at two; omega
  have lb := shores_add_two_le_graph_order ab cd
  have hC : 3≤(Shore C).card := by
    have h : (cutPorts C).card≤(Shore C).card := card_le_card (filter_subset _ _)
    omega
  have min2 := pair_deletion_min_degree_two (G:=G) (by omega) conn
  apply traceable_of_complementary_wings ab (shore_disjoint cd) (shore_off C).1 (shore_off C).2
    (shore_off D).1 (shore_off D).2 cover
  rcases three_five_shore_cardinality_cases hc two even degree cd cover C3 D5 xc ax bx with
    ⟨c4,d8,dh⟩|⟨c6,d7⟩|⟨c7,d5⟩
  · exact .inl ⟨terminal_route_on_three_port_small_shore hc even degree cd C3 D5 (.inl c4) xc ax bx,
      free_route_on_five_port_side_opposite_three hc even degree min2 cd C3 D5 (.inr ⟨d8,dh⟩)⟩
  · exact .inl ⟨terminal_route_on_three_port_small_shore hc even degree cd C3 D5 (.inr c6) xc ax bx,
      free_route_on_five_port_side_opposite_three hc even degree min2 cd C3 D5 (.inl d7)⟩
  exact .inr ⟨terminal_mask_of_five_vertex_all_port_shore degree D5 d5 yd ay by',
    free_route_on_three_port_seven_shore hc even degree min2 cd D5 c7 xc ax bx⟩

#print axioms traceable_of_actual_five_three_five_ports
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
