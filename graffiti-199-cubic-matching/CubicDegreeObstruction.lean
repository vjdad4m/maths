import CubicEdgeCuts

namespace Graffiti199Depleted.Catalogue.CubicDegreeObstruction

open SimpleGraph

abbrev V := Fin 3 ⊕ Fin 12
private abbrev Skeleton := Fin 3 ⊕ Fin 5

private def low (i : Fin 3) : V := .inl i
private def hub (i : Fin 12) : V := .inr i
private def hubPort (i : Fin 5) : Fin 12 := i.castLE (by decide)
private def owner (i : Fin 5) : Fin 3 := if i.val < 2 then 0 else if i.val = 2 then 1 else 2
private def consecutive (i j : Fin 3) := i.val + 1 = j.val ∨ j.val + 1 = i.val

private def adjacent : V → V → Prop
  | .inl i, .inl j => consecutive i j
  | .inl i, .inr p => ∃ j : Fin 5, hubPort j = p ∧ owner j = i
  | .inr p, .inl i => ∃ j : Fin 5, hubPort j = p ∧ owner j = i
  | .inr p, .inr q => p ≠ q

/-- A 12-clique with a cubic three-vertex path attached at five
distinct ports, two at each end and one at the middle. -/
def graph : SimpleGraph V where
  Adj := adjacent
  symm := by
    rintro (i|i) (j|j) h
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    rintro (i|i)
    · change ¬ (i.val + 1 = i.val ∨ i.val + 1 = i.val)
      omega
    · exact fun h => h rfl

instance decidableAdj : DecidableRel graph.Adj := by
  rintro (i|i) (j|j)
  · change Decidable (i.val + 1 = j.val ∨ j.val + 1 = i.val)
    infer_instance
  · change Decidable (∃ k : Fin 5, hubPort k = j ∧ owner k = i)
    infer_instance
  · change Decidable (∃ k : Fin 5, hubPort k = i ∧ owner k = j)
    infer_instance
  · change Decidable (i ≠ j)
    infer_instance

private def skeletonEmbed : Skeleton ↪ V :=
  ⟨Sum.map id hubPort,by
    intro x y eq
    rcases x with i|p <;> rcases y with j|q
    · exact congrArg Sum.inl (Sum.inl.inj eq)
    · cases eq
    · cases eq
    · have same : hubPort p = hubPort q :=
        Sum.inr.inj (show hub (hubPort p) = hub (hubPort q) from eq)
      have vals := congrArg (fun z : Fin 12 => z.val) same
      exact congrArg Sum.inr (Fin.ext vals)⟩

private def touches (i : Fin 3) : Skeleton → Prop
  | .inl j => consecutive i j
  | .inr j => owner j = i

private instance (i : Fin 3) : DecidablePred (touches i) := by
  rintro (j|j)
  · change Decidable (i.val + 1 = j.val ∨ j.val + 1 = i.val)
    infer_instance
  · change Decidable (owner j = i)
    infer_instance

private theorem touches_edge {i : Fin 3} {z : Skeleton} (h : touches i z) :
    graph.Adj (low i) (skeletonEmbed z) := by
  rcases z with j|j
  · exact h
  · exact ⟨j,rfl,h⟩

private def outside (S : Finset (Fin 3)) : Skeleton → Prop
  | .inl j => j ∉ S
  | .inr _ => True

private instance (S : Finset (Fin 3)) : DecidablePred (outside S) := by
  rintro (j|j)
  · change Decidable (j ∉ S)
    infer_instance
  · change Decidable True
    infer_instance

private def boundary (S : Finset (Fin 3)) : Finset Skeleton :=
  Finset.univ.filter (fun z => outside S z ∧ ∃ i ∈ S, touches i z)

private theorem boundary_size : ∀ S : Finset (Fin 3), 0 < S.card →
    3 ≤ (boundary S).card ∧ (2 ≤ S.card → 4 ≤ (boundary S).card) := by decide

private abbrev H (D : Finset V) := graph.induce {v | v ∉ D}
private abbrev Remains (D : Finset V) := {v : V // v ∉ D}

private def hubs : Finset V :=
  Finset.univ.map (⟨hub,fun _ _ h => Sum.inr.inj h⟩ : Fin 12 ↪ V)

private theorem survives_hub (D : Finset V) (small : D.card ≤ 3) : ∃ h, hub h ∉ D := by
  have cb : hubs.card = 12 := by simp [hubs]
  obtain ⟨z,member,off⟩ := Finset.exists_mem_not_mem_of_card_lt_card (show D.card < hubs.card by omega)
  obtain ⟨h,_,rfl⟩ := Finset.mem_map.mp member
  exact ⟨h,off⟩

private theorem hub_reachable {D : Finset V} {h k : Fin 12}
    (hh : hub h ∉ D) (hk : hub k ∉ D) :
    (H D).Reachable ⟨hub h,hh⟩ ⟨hub k,hk⟩ := by
  by_cases eq : h = k
  · subst k
    exact .rfl
  · exact (show (H D).Adj ⟨hub h,hh⟩ ⟨hub k,hk⟩ from eq).reachable

private theorem disconnected_boundary {D : Finset V} {h : Fin 12} (hh : hub h ∉ D)
    {u : Remains D} (no : ¬ (H D).Reachable u ⟨hub h,hh⟩) :
    ∃ S : Finset (Fin 3), (boundary S).card ≤ D.card ∧
      (∀ w : Remains D, (H D).Reachable u w →
        ∃ i ∈ S, low i = w.val) := by
  classical
  let S : Finset (Fin 3) :=
    Finset.univ.filter (fun i => ∃ hi : low i ∉ D, (H D).Reachable u ⟨low i,hi⟩)
  have memS (i : Fin 3) : i ∈ S ↔ ∃ hi : low i ∉ D, (H D).Reachable u ⟨low i,hi⟩ := by
    simp [S]
  have sub : (boundary S).map skeletonEmbed ⊆ D := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨out,i,hi,touch⟩ := (Finset.mem_filter.mp hw).2
    obtain ⟨iKeep,ui⟩ := (memS i).mp hi
    by_contra off
    have edge : (H D).Adj ⟨low i,iKeep⟩ ⟨skeletonEmbed w,off⟩ := touches_edge touch
    have uw := ui.trans edge.reachable
    rcases w with j|j
    · exact (show j ∉ S from out) ((memS j).mpr ⟨off,uw⟩)
    · exact no (uw.trans (hub_reachable (k := h) off hh))
  have count := Finset.card_le_card sub
  rw [Finset.card_map] at count
  refine ⟨S,count,?_⟩
  rintro ⟨i|k,keep⟩ reach
  · exact ⟨i,(memS i).mpr ⟨keep,reach⟩,rfl⟩
  · exact (no (reach.trans (hub_reachable (k := h) keep hh))).elim

theorem connectivity_at_least_three : ConnectivityAtLeast graph 3 := by
  refine ⟨by decide,?_⟩
  intro D small
  obtain ⟨h,hh⟩ := survives_hub D (by omega)
  let anchor : Remains D := ⟨hub h,hh⟩
  have reach (u : Remains D) : (H D).Reachable u anchor := by
    by_contra no
    obtain ⟨S,count,cover⟩ := disconnected_boundary hh no
    obtain ⟨i,hi,_⟩ := cover u .rfl
    have pos := Finset.card_pos.mpr ⟨i,hi⟩
    have three := (boundary_size S pos).1
    omega
  exact @SimpleGraph.Connected.mk _ (H D) (fun x y => (reach x).trans (reach y).symm) ⟨anchor⟩

theorem crossing_law : CrossingBetweenSurvivingEdges graph := by
  apply edgeReach_iff_crossing_between_surviving_edges.mp
  intro D small a b c d ab cd
  obtain ⟨h,hh⟩ := survives_hub D small
  let anchor : Remains D := ⟨hub h,hh⟩
  have reach {u v : Remains D} (uv : (H D).Adj u v) : (H D).Reachable u anchor := by
    by_contra no
    obtain ⟨S,count,cover⟩ := disconnected_boundary hh no
    obtain ⟨i,hi,ui⟩ := cover u .rfl
    obtain ⟨j,hj,vj⟩ := cover v uv.reachable
    have ne : i ≠ j := fun eq => uv.ne (Subtype.ext (ui.symm.trans ((congrArg low eq).trans vj)))
    have two : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨i,hi,j,hj,ne⟩
    have four := (boundary_size S (by omega)).2 two
    omega
  exact (reach ab).trans (reach cd).symm

private theorem cubic_low : ∀ i : Fin 3, graph.degree (low i) = 3 := by decide

theorem exact_connectivity : vertexConnectivity graph = 3 := by
  classical
  apply Nat.le_antisymm
  · by_contra! tooLarge
    let u := low 0
    let D := graph.neighborFinset u
    have small : D.card = 3 := (graph.card_neighborFinset_eq_degree u).trans (cubic_low 0)
    have uD : u ∉ D := graph.not_mem_neighborFinset_self u
    obtain ⟨h,hh⟩ := survives_hub D small.le
    let x : Remains D := ⟨u,uD⟩
    let y : Remains D := ⟨hub h,hh⟩
    have isolated (w : Remains D) (e : (H D).Adj x w) : False :=
      w.property ((graph.mem_neighborFinset _ _).mpr e)
    have conn := connectivityAtLeast_vertexConnectivity (G := graph)
    obtain ⟨p⟩ := (conn.2 D (by omega)).preconnected x y
    have eq {w : Remains D} (q : (H D).Walk x w) : x = w := by
      cases q with
      | nil => rfl
      | cons e _ => exact (isolated _ e).elim
    cases congrArg Subtype.val (eq p)
  · unfold vertexConnectivity
    exact Finset.le_sup (f := id) (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr connectivity_at_least_three.1,connectivity_at_least_three⟩)

private theorem no_triangle_in_tree {X : Type*} {K : SimpleGraph X} (tree : K.IsTree)
    {a b c : X} (ab : K.Adj a b) (ac : K.Adj a c) (bc : K.Adj b c) : False := by
  have unique := (SimpleGraph.isTree_iff_existsUnique_path.mp tree).2 a b
  let p := ab.toWalk
  let q := SimpleGraph.Walk.cons ac bc.symm.toWalk
  have pathP : p.IsPath := by simp [p,SimpleGraph.Adj.toWalk,SimpleGraph.Walk.isPath_def,ab.ne]
  have pathQ : q.IsPath := by
    simp [q,SimpleGraph.Adj.toWalk,SimpleGraph.Walk.isPath_def,ab.ne,ac.ne,bc.ne.symm]
  have len := congrArg SimpleGraph.Walk.length (unique.unique pathP pathQ)
  exact (by decide : (1 : ℕ) ≠ 2) len

private def lows : Finset V :=
  Finset.univ.map (⟨low,fun _ _ h => Sum.inl.inj h⟩ : Fin 3 ↪ V)

private theorem hub_of {S : Finset V} {x : V} (h : x ∈ S ∩ hubs) :
    ∃ i : Fin 12, hub i = x := by
  obtain ⟨i,_,eq⟩ := Finset.mem_map.mp (Finset.mem_inter.mp h).2
  exact ⟨i,eq⟩

private theorem card_le_hubs_add_three (S : Finset V) :
    S.card ≤ (S ∩ hubs).card + 3 := by
  have sub : S ⊆ lows ∪ (S ∩ hubs) := by
    rintro (i|h) mem
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr
        ⟨mem,Finset.mem_map.mpr ⟨h,Finset.mem_univ _,rfl⟩⟩))
  have lc : lows.card = 3 := by simp [lows]
  have bound := (Finset.card_le_card sub).trans (Finset.card_union_le lows (S ∩ hubs))
  omega

theorem no_independent_six : NoIndependentSix graph := by
  intro S size
  have count := card_le_hubs_add_three S
  obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp (show 1 < (S ∩ hubs).card by omega)
  obtain ⟨i,rfl⟩ := hub_of ha
  obtain ⟨j,rfl⟩ := hub_of hb
  exact ⟨hub i,(Finset.mem_inter.mp ha).1,hub j,(Finset.mem_inter.mp hb).1,
    fun eq => ne (congrArg hub eq)⟩

theorem tree_budget : treeNumber graph ≤ 5 := by
  classical
  unfold treeNumber
  apply Finset.sup_le
  intro S mem
  have tree := (Finset.mem_filter.mp mem).2
  let K := graph.induce (↑S : Set V)
  let A := S ∩ hubs
  have cap : A.card ≤ 2 := by
    by_contra! many
    obtain ⟨a,ma,b,mb,c,mc,ab,ac,bc⟩ := Finset.two_lt_card.mp many
    obtain ⟨i,rfl⟩ := hub_of ma
    obtain ⟨j,rfl⟩ := hub_of mb
    obtain ⟨k,rfl⟩ := hub_of mc
    exact no_triangle_in_tree tree
      (show K.Adj ⟨hub i,(Finset.mem_inter.mp ma).1⟩ ⟨hub j,(Finset.mem_inter.mp mb).1⟩
        from fun eq => ab (congrArg hub eq))
      (show K.Adj ⟨hub i,(Finset.mem_inter.mp ma).1⟩ ⟨hub k,(Finset.mem_inter.mp mc).1⟩
        from fun eq => ac (congrArg hub eq))
      (show K.Adj ⟨hub j,(Finset.mem_inter.mp mb).1⟩ ⟨hub k,(Finset.mem_inter.mp mc).1⟩
        from fun eq => bc (congrArg hub eq))
  have bound := card_le_hubs_add_three S
  change (S ∩ hubs).card ≤ 2 at cap
  omega

private def path : List V :=
  [hub 0,low 0,low 1,low 2,hub 3,hub 1,hub 2,hub 4,hub 5,
    hub 6,hub 7,hub 8,hub 9,hub 10,hub 11]

theorem traceable : Traceable graph := by
  apply traceable_iff_hamiltonian_walk.mpr
  apply pathOn_univ_iff_hamiltonian_walk.mp
  refine ⟨⟨path,by decide,by decide,by decide,?_⟩⟩
  rintro (i|j)
  · fin_cases i <;> simp [path,hub,low]
  · fin_cases j <;> simp [path,hub,low]

private theorem cubic_edge_has_cubic_neighbor_compute :
    ∀ u v : V, graph.Adj u v → graph.degree u = 3 → graph.degree v = 3 →
      ∃ x : V, x ≠ u ∧ x ≠ v ∧ (graph.Adj x u ∨ graph.Adj x v) ∧ graph.degree x = 3 := by
  decide

theorem cubic_edge_has_cubic_neighbor {u v : V}
    (uv : graph.Adj u v) (du : graph.degree u = 3) (dv : graph.degree v = 3) :
    ∃ x ∈ edgeBoundary graph u v, graph.degree x = 3 := by
  obtain ⟨x,xu,xv,edges,dx⟩ := cubic_edge_has_cubic_neighbor_compute u v uv du dv
  exact ⟨x,mem_edgeBoundary.mpr ⟨xu,xv,edges⟩,dx⟩

private theorem middle_of_cubic_edge :
    ∀ u v : V, graph.Adj u v → graph.degree u = 3 → graph.degree v = 3 →
      u = low 1 ∨ v = low 1 := by decide

private theorem middle_neighbors_independent :
    ∀ x y : V, graph.Adj (low 1) x → graph.Adj (low 1) y → ¬ graph.Adj x y := by decide

theorem no_full_pair : IsEmpty (FullPair graph) := by
  refine ⟨fun P => ?_⟩
  have lowEdge := P.edges 0 1 (by decide)
  rcases middle_of_cubic_edge _ _ lowEdge (P.degree 0 (by decide)) (P.degree 1 (by decide)) with a|b
  · exact middle_neighbors_independent _ _ (a ▸ P.edges 0 2 (by decide))
      (a ▸ P.edges 0 3 (by decide)) (P.edges 2 3 (by decide))
  · exact middle_neighbors_independent _ _ (b ▸ P.edges 1 4 (by decide))
      (b ▸ P.edges 1 5 (by decide)) (P.edges 4 5 (by decide))

/-- The verified cut and tree hypotheses alone do not guarantee a
cubic edge whose other neighbors all have degree different from three. -/
theorem order_fifteen_degree_obstruction :
    Fintype.card V = 15 ∧ vertexConnectivity graph = 3 ∧ CrossingBetweenSurvivingEdges graph ∧
      treeNumber graph ≤ 5 ∧ NoIndependentSix graph ∧ Traceable graph ∧
      IsEmpty (FullPair graph) ∧
      (∃ u v, graph.Adj u v ∧ graph.degree u = 3 ∧ graph.degree v = 3) ∧
      ¬ (∃ u v, graph.Adj u v ∧ graph.degree u = 3 ∧ graph.degree v = 3 ∧
        ∀ x ∈ edgeBoundary graph u v, graph.degree x ≠ 3) := by
  refine ⟨by decide,exact_connectivity,crossing_law,tree_budget,no_independent_six,traceable,no_full_pair,
    ⟨low 0,low 1,by decide,cubic_low 0,cubic_low 1⟩,?_⟩
  rintro ⟨u,v,edge,du,dv,all⟩
  obtain ⟨x,hx,dx⟩ := cubic_edge_has_cubic_neighbor edge du dv
  exact all x hx dx

#print axioms crossing_law
#print axioms exact_connectivity
#print axioms order_fifteen_degree_obstruction

end Graffiti199Depleted.Catalogue.CubicDegreeObstruction
