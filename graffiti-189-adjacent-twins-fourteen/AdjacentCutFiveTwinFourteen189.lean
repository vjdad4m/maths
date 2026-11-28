import AdjacentCutFiveTwinThreeGeom189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_closed shore_off shore_disjoint shore_hit_a from AdjacentCutFiveActual189
open private positive_cap degree_le_shore_add_one from AdjacentCutFiveComponents189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
open private mem_positive from AdjacentCutFiveBound189
open private twin_partition twin_even_budget glue_twin_shore_routes twin_shore_root_of_near twin_port_close from AdjacentCutFiveTwinBothFour189
open private global_degree_le_inside_add_two global_degree_le_inside_if_dark twin_shore_root_from_ore
  twin_shore_root_of_three_foreign from AdjacentCutFiveTwinThreeGeom189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem even_other_le_three
    (hc : G.Connected) (ab : a≠b) (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (twin : ∀ z, z≠a → z≠b → (G.Adj a z ↔ G.Adj b z))
    {C D : Cmp G a b} (cd : C≠D) (exist : (AdjTwinEven C).Nonempty) :
    (AdjTwinEven D).card≤3 := by
  classical
  obtain ⟨x,xe⟩ := exist
  obtain ⟨xc,ea⟩ := mem_filter.mp xe
  have xa : x≠a := fun e=>(shore_off C).1 (e ▸ xc)
  have xb : x≠b := fun e=>(shore_off C).2 (e ▸ xc)
  have xt := twin_dist_on_shore hc twin xc
  have posa : a∈PositiveEven G x :=
    mem_positive.mpr ⟨xa.symm,by rwa [dist_comm]⟩
  have posb : b∈PositiveEven G x :=
    mem_positive.mpr ⟨xb.symm,by rwa [dist_comm,←xt]⟩
  have subf : AdjTwinEven D⊆PositiveEven G x := by
    intro z ze
    obtain ⟨zd,za⟩ := mem_filter.mp ze
    have outside : z∉Shore C := fun w=>disjoint_left.mp (shore_disjoint cd) w zd
    have neq : z≠x := fun e=>outside (e.symm ▸ xc)
    have f := cross_metric (Shore C) hc xc outside (shore_closed C)
    rw [dist_comm (G:=G) (u:=x) (v:=a),dist_comm (G:=G) (u:=x) (v:=b),
      ←xt,←twin_dist_on_shore hc twin zd,min_self] at f
    exact mem_positive.mpr ⟨neq,f ▸ ea.add za⟩
  have sub : insert a (insert b (AdjTwinEven D))⊆PositiveEven G x := by
    intro z zm
    rcases mem_insert.mp zm with rfl|zm
    · exact posa
    rcases mem_insert.mp zm with rfl|zm
    · exact posb
    · exact subf zm
  have ao : a∉insert b (AdjTwinEven D) := by
    intro h
    rcases mem_insert.mp h with e|h
    · exact ab e
    · exact (shore_off D).1 (mem_filter.mp h).1
  have bo : b∉AdjTwinEven D := fun h=>(shore_off D).2 (mem_filter.mp h).1
  have q := card_le_card sub
  rw [card_insert_of_not_mem ao,card_insert_of_not_mem bo] at q
  have c := positive_cap x even
  omega

private theorem twin_route_small_shore
    (ab : a ≠ b)
    (twin : ∀ z, z≠a → z≠b → (G.Adj a z ↔ G.Adj b z))
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C : Cmp G a b} (lo : 2≤(Shore C).card) (hi : (Shore C).card≤6) :
    ∃ s t,G.Adj a s ∧ RouteOn G (Shore C) s t := by
  apply twin_shore_root_from_ore degree twin ab conn lo
  intro u uc v vc uv no hu hv
  have d := global_degree_le_inside_add_two uc
  have e := global_degree_le_inside_add_two vc
  omega

theorem traceable_of_adjacent_twins_two_shores_order_ge_fourteen
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (twin : ∀ z, z≠a → z≠b → (G.Adj a z ↔ G.Adj b z))
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (two : Nat.card (Cmp G a b) = 2)
    (n : 14≤Fintype.card V) :
    ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨C,D,cd,cover⟩ := actual_two_shores two
  have run {K L : Cmp G a b} (kl : K≠L)
      (cover : ∀ {z : V}, z≠a → z≠b → z∈Shore K ∨ z∈Shore L)
      (ko : (AdjTwinOdd K).card≤3) :
      ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
    obtain ⟨x,xk,ax⟩ := shore_hit_a ab.ne conn K
    obtain ⟨y,yl,ay⟩ := shore_hit_a ab.ne conn L
    have ka := (card_le_card (adj_twin_odd_foreign hc twin kl.symm yl ay)).trans (positive_cap y even)
    have la := (card_le_card (adj_twin_odd_foreign hc twin kl xk ax)).trans (positive_cap x even)
    have ke := twin_even_budget even kl
    have kp : (AdjTwinOdd K).card+(AdjTwinEven K).card=(Shore K).card := twin_partition
    have lp : (AdjTwinOdd L).card+(AdjTwinEven L).card=(Shore L).card := twin_partition
    have sub : (univ.erase a |>.erase b : Finset V) ⊆ Shore K ∪ Shore L := by
      intro z hz
      exact mem_union.mpr (cover (mem_erase.mp (mem_erase.mp hz).2).1 (mem_erase.mp hz).1)
    have cnt := card_le_card sub
    rw [card_erase_of_mem (by simp [ab.ne.symm]),card_erase_of_mem (mem_univ _),
      card_univ,card_union_of_disjoint (shore_disjoint kl)] at cnt
    have k2 : 2≤(AdjTwinOdd K).card := by omega
    have l4 : 4≤(AdjTwinOdd L).card := by omega
    have ks2 : 2≤(Shore K).card := by omega
    have ls2 : 2≤(Shore L).card := by omega
    have ks4 : 4≤(Shore K).card := by
      by_contra hn
      obtain ⟨u,uk,v,vk,uv⟩ := one_lt_card.mp ks2
      have du := degree_le_shore_add_one K uk
      have dv := degree_le_shore_add_one K vk
      rcases degree u v uv with e|e <;> omega
    have rk : ∃ s t,G.Adj a s ∧ RouteOn G (Shore K) s t :=
      twin_shore_root_of_near hc degree twin ab.ne conn ks4 (by omega)
        (fun _ uk au=>twin_port_close hc even twin conn kl l4 uk au)
    by_cases l6 : (Shore L).card≤6
    · exact glue_twin_shore_routes ab twin kl cover rk
        (twin_route_small_shore ab.ne twin conn degree ls2 l6)
    have kp' : (AdjTwinEven K).Nonempty := card_pos.mp (by omega)
    have l3 : (AdjTwinEven L).card≤3 := even_other_le_three hc ab.ne even twin kl kp'
    have l8 : (Shore L).card≤8 := by omega
    have lp' : (AdjTwinEven L).Nonempty := card_pos.mp (by omega)
    have k3 : (AdjTwinEven K).card≤3 := even_other_le_three hc ab.ne even twin kl.symm lp'
    have ko3 : 3≤(AdjTwinOdd K).card := by
      by_contra no
      have kdark : 2≤(AdjTwinEven K).card := by omega
      obtain ⟨u,ue,v,ve,uv⟩ := one_lt_card.mp kdark
      have uLow (w : V) (we : w∈AdjTwinEven K) : G.degree w<5 := by
        obtain ⟨wk,ee⟩ := mem_filter.mp we
        have wa : w≠a := fun e=>(shore_off K).1 (e ▸ wk)
        have na : ¬G.Adj a w := by
          intro e
          rw [dist_eq_one_iff_adj.mpr e] at ee
          exact (by decide : ¬Even (1:ℕ)) ee
        have nb : ¬G.Adj b w := fun h=>na ((twin w wa h.ne.symm).mpr h)
        have d := global_degree_le_inside_if_dark wk na nb
        have sub : ArticulationPair.inside G (Shore K) w ⊆ (Shore K).erase w := by
          intro z zz
          exact mem_erase.mpr ⟨(mem_filter.mp zz).2.ne.symm,(mem_filter.mp zz).1⟩
        have c := card_le_card sub
        rw [card_erase_of_mem wk] at c
        omega
      rcases degree u v uv with e|e
      · exact (Nat.not_le_of_gt (uLow u ue)) e
      · exact (Nat.not_le_of_gt (uLow v ve)) e
    exact glue_twin_shore_routes ab twin kl cover rk
      (twin_shore_root_of_three_foreign hc even twin ab.ne conn degree kl.symm ko3
        (by omega) l8)
  by_cases c : (AdjTwinOdd C).card≤3
  · exact run cd cover c
  by_cases d : (AdjTwinOdd D).card≤3
  · exact run cd.symm (fun za zb=>(cover za zb).symm) d
  exact traceable_of_adjacent_twins_two_odd_four hc ab even twin conn degree cd cover
    (Nat.lt_of_not_ge c) (Nat.lt_of_not_ge d)

#print axioms traceable_of_adjacent_twins_two_shores_order_ge_fourteen
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
