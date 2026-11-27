import DegreeFiveThreeFiveBound189
import DegreeFiveOppNonportFour189
import DegreeFiveBothFourFiveFifteenClose189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset
open private Shore shore_off shore_closed shore_disjoint from DegreeFiveActualCut189
open private Cmp from DegreeFiveThreeForeignImpossible189
open private secondShore four_in_nonsingleton from DegreeFiveDistanceTwoThreeClose189
open private d2 from CrossSaturation189
open private sharedPortSet inside_high_at_least_three from DegreeFiveBalancedCommonRoot189
open private shores_add_two_le_graph_order from DegreeFiveBothFourFiveFifteenClose189
open private graph_order_le_shores_add_two from DegreeFiveBothNonsaturated189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem nonport_neighbors_subset {C : Cmp (G:=G) (a:=a) (b:=b)} {z : V}
    (zc : z∈Shore C) (zn : z∉cutPorts C) :
    G.neighborFinset z⊆(Shore C).erase z := by
  intro w wp
  have zw := (mem_neighborFinset G z w).mp wp
  rcases shore_closed C z zc w zw with rfl|rfl|wc
  · exact (zn (mem_filter.mpr ⟨zc,.inl zw.symm⟩)).elim
  · exact (zn (mem_filter.mpr ⟨zc,.inr zw.symm⟩)).elim
  exact mem_erase.mpr ⟨zw.ne.symm,wc⟩

private theorem nonport_degree_bound_small {C : Cmp (G:=G) (a:=a) (b:=b)} {z : V}
    (zc : z∈Shore C) (zn : z∉cutPorts C) :
    G.degree z+1≤(Shore C).card := by
  have le := card_le_card (nonport_neighbors_subset zc zn)
  rw [card_neighborFinset_eq_degree,card_erase_of_mem zc] at le
  have pos := card_pos.mpr ⟨z,zc⟩
  omega

theorem three_five_shore_cardinality_cases
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    (cover : ∀ z : V,z=a ∨ z=b ∨ z∈Shore C ∨ z∈Shore D)
    (C3 : (cutPorts C).card=3) (D5 : (cutPorts D).card=5)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    ((Shore C).card=4 ∧ (Shore D).card≤8 ∧ ∀ w∈Shore D,5≤G.degree w) ∨
    ((Shore C).card=6 ∧ (Shore D).card≤7) ∨
    ((Shore C).card=7 ∧ (Shore D).card=5) := by
  classical
  have ab : a≠b := by intro e; rw [e,dist_self] at two; omega
  have lb := shores_add_two_le_graph_order ab cd
  have ub := three_five_order_bound_by_double_charges hc two even cd cover C3 D5 xc ax bx
  have c4 : 4≤(Shore C).card := by
    apply four_in_nonsingleton degree
    have h : (cutPorts C).card≤(Shore C).card := card_le_card (filter_subset _ _)
    omega
  have d5 : 5≤(Shore D).card := by
    have h : (cutPorts D).card≤(Shore D).card := card_le_card (filter_subset _ _)
    omega
  let E := Shore C \ cutPorts C
  have eCount : E.card+3=(Shore C).card := by
    have h : E.card+(cutPorts C).card=(Shore C).card :=
      card_sdiff_add_card_eq_card (filter_subset _ _)
    rwa [C3] at h
  have low (z : V) (ze : z∈E) (small : (Shore C).card≤5) : ¬5≤G.degree z := by
    obtain ⟨zc,zn⟩ := mem_sdiff.mp ze
    have m := nonport_degree_bound_small zc zn
    omega
  have cNot5 : (Shore C).card≠5 := by
    intro n
    obtain ⟨u,ue,v,ve,uv⟩ := one_lt_card.mp (show 1<E.card by omega)
    exact (degree u v uv).elim (low u ue (by omega)) (low v ve (by omega))
  by_cases small : (Shore C).card=4
  · obtain ⟨z,ze⟩ := card_pos.mp (show 0<E.card by omega)
    have zlow := low z ze (by omega)
    obtain ⟨zc,zn⟩ := mem_sdiff.mp ze
    have za : ¬G.Adj a z := fun h=>zn (mem_filter.mpr ⟨zc,.inl h⟩)
    have zb : ¬G.Adj b z := fun h=>zn (mem_filter.mpr ⟨zc,.inr h⟩)
    have xz := common_universal_in_shore_at_five hc even cd xc ax bx D5 z zc
      (fun e=>za (e ▸ ax))
    let F := Shore D \ cutPorts D
    have fN : F.card+5=(Shore D).card := by
      have h : F.card+(cutPorts D).card=(Shore D).card :=
        card_sdiff_add_card_eq_card (filter_subset _ _)
      rwa [D5] at h
    have za2 := d2 hc (show z≠a from fun e=>(shore_off C).1 (e ▸ zc)) (fun e=>za e.symm) xz.symm ax.symm
    have zb2 := d2 hc (show z≠b from fun e=>(shore_off C).2 (e ▸ zc)) (fun e=>zb e.symm) xz.symm bx.symm
    have noF : Disjoint ({z,a,b} : Finset V) F := by
      refine disjoint_left.mpr ?_
      intro u uh uf
      have ud := (mem_sdiff.mp uf).1
      simp only [mem_insert,mem_singleton] at uh
      rcases uh with rfl|rfl|rfl
      · exact disjoint_left.mp (shore_disjoint cd) zc ud
      · exact (shore_off D).1 ud
      exact (shore_off D).2 ud
    have subset : ({z,a,b} : Finset V)∪F ⊆ EvenFrom G z := by
      intro u hu
      rcases mem_union.mp hu with h|h
      · simp only [mem_insert,mem_singleton] at h
        apply mem_filter.mpr
        refine ⟨mem_univ _,?_⟩
        rcases h with h|h|h
        · rw [h,dist_self]
          decide
        · have hh : G.dist z a=2 := by simpa [DistanceTwo] using za2
          rw [h,hh]
          decide
        have hh : G.dist z b=2 := by simpa [DistanceTwo] using zb2
        rw [h,hh]
        decide
      obtain ⟨ud,un⟩ := mem_sdiff.mp h
      have lower := opposite_nonporters_dist_at_least_four hc cd zc ud zn un
      have ecc := (saturated_common_foreign_port_domination hc even cd D5 xc ax bx).1 u
      have tri := hc.dist_triangle (u:=z) (v:=x) (w:=u)
      have edge := dist_eq_one_iff_adj.mpr xz.symm
      have eq : G.dist z u=4 := by omega
      exact mem_filter.mpr ⟨mem_univ _,by rw [eq]; decide⟩
    have count : ({z,a,b} : Finset V).card=3 := by
      have zne : z∉({a,b} : Finset V) := by
        simp [show z≠a from fun e=>(shore_off C).1 (e ▸ zc),
          show z≠b from fun e=>(shore_off C).2 (e ▸ zc)]
      rw [card_insert_of_not_mem zne]
      simp [ab]
    refine .inl ⟨small,?_,?_⟩
    · have cap := (card_le_card subset).trans (even z)
      rw [card_union_of_disjoint noF,count] at cap
      omega
    intro w wd
    exact (degree z w (fun e=>disjoint_left.mp (shore_disjoint cd) zc (e.symm ▸ wd))).resolve_left zlow
  by_cases mid : (Shore C).card=6
  · exact .inr (.inl ⟨mid,by omega⟩)
  exact .inr (.inr ⟨by omega,by omega⟩)

#print axioms three_five_shore_cardinality_cases
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
