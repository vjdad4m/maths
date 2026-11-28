import AdjacentCutFiveTwinFourteen189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_closed shore_off shore_connected shore_disjoint from AdjacentCutFiveActual189
open private positive_cap from AdjacentCutFiveComponents189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
open private mem_positive cross_dist_of_equal odd_dist_to_even_next from AdjacentCutFiveBound189
open private lift_side_path from DegreeFiveSmallSides189
open private global_degree_le_inside_add_two from AdjacentCutFiveTwinThreeGeom189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

noncomputable def EqualOddShore (D : Cmp G a b) : Finset V :=
  (Shore D).filter (fun v=>G.dist a v=G.dist b v ∧ ¬Even (G.dist a v))

noncomputable def CommonAdjPorts (D : Cmp G a b) : Finset V :=
  (Shore D).filter (fun v=>G.Adj a v ∧ G.Adj b v)

private theorem common_port_close_of_equal_odd
    (hc : G.Connected) (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    {C D : Cmp G a b} (cd : C≠D) (four : 4≤(EqualOddShore D).card)
    {x : V} (xC : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x) :
    ((Shore C)∩DistanceTwo G x).card≤1 ∧ ∀ z∈Shore C,G.dist x z≤2 := by
  classical
  let Q := (Shore C)∩DistanceTwo G x
  have foreign : EqualOddShore D⊆PositiveEven G x := by
    intro z zm
    obtain ⟨zd,e,odd⟩ := mem_filter.mp zm
    have zo : z∉Shore C := fun w=>disjoint_left.mp (shore_disjoint cd) w zd
    have h := cross_dist_of_equal (Shore C) hc xC zo (shore_closed C) (.inl ax) e
    exact mem_positive.mpr ⟨fun q=>zo (q.symm ▸ xC),odd_dist_to_even_next h odd⟩
  have local' : Q ⊆ PositiveEven G x := by
    intro z hz
    have e : G.dist x z = 2 := by simpa [DistanceTwo] using (mem_inter.mp hz).2
    exact mem_positive.mpr ⟨fun h=>by rw [h,dist_self] at e; omega,by simp [e]⟩
  have dis : Disjoint Q (EqualOddShore D) :=
    (shore_disjoint cd).mono inter_subset_left (filter_subset _ _)
  have ct := card_le_card (union_subset local' foreign)
  rw [card_union_of_disjoint dis] at ct
  have cap := positive_cap x even
  have c1 : Q.card≤1 := by omega
  refine ⟨c1,?_⟩
  intro z zL
  apply Classical.byContradiction
  intro bad
  have d3 : 3≤G.dist x z := by omega
  let U := (↑Q : Set V)ᶜ
  have zz : z∈U := by
    intro c
    have h : z∈Q := c
    have hh : G.dist x z=2 := by simpa [DistanceTwo] using (mem_inter.mp h).2
    omega
  have xx : x∈U := by
    intro c
    have h : x∈Q := c
    have hh : G.dist x x=2 := by simpa [DistanceTwo] using (mem_inter.mp h).2
    rw [SimpleGraph.dist_self] at hh
    omega
  have c := conn Q (by omega)
  have imp {u v : U} (p : (G.induce U).Walk u v) :
      u.val∈Shore C ∧ 3≤G.dist x u.val → v.val∈Shore C ∧ 3≤G.dist x v.val := by
    induction p with
    | nil => exact id
    | @cons u w v e p ih =>
      intro ⟨lu,du⟩
      apply ih
      change G.Adj u.val w.val at e
      have tri := hc.dist_triangle (u:=x) (v:=w.val) (w:=u.val)
      have dw := dist_eq_one_iff_adj.mpr e.symm
      have wa := dist_eq_one_iff_adj.mpr ax.symm
      have wb := dist_eq_one_iff_adj.mpr bx.symm
      rcases shore_closed C u.val lu w.val e with h|h|lw
      · rw [h] at tri dw
        omega
      · rw [h] at tri dw
        omega
      refine ⟨lw,?_⟩
      apply Classical.byContradiction
      intro small
      have l2 : G.dist x w.val=2 := by omega
      have cm : w.val∈Q := mem_inter.mpr ⟨lw,by simp [DistanceTwo,l2]⟩
      exact w.property cm
  obtain ⟨p⟩ := c.preconnected (⟨z,zz⟩ : U) ⟨x,xx⟩
  have impossible := (imp p ⟨zL,d3⟩).2
  change 3≤G.dist x x at impossible
  rw [SimpleGraph.dist_self] at impossible
  omega



private theorem global_degree_le_inside_add_one_of_noncommon
    {C : Cmp G a b} {x : V} (xc : x∈Shore C)
    (no : ¬(G.Adj a x ∧ G.Adj b x)) :
    G.degree x≤(ArticulationPair.inside G (Shore C) x).card+1 := by
  classical
  let N := ArticulationPair.inside G (Shore C) x
  have combine {s t : V} (sx : ¬G.Adj s x)
      (cover : ∀ z,G.Adj x z → z=s ∨ z=t ∨ z∈Shore C) :
      G.degree x≤N.card+1 := by
    have sub : G.neighborFinset x⊆insert t N := by
      intro z zz
      have e := (mem_neighborFinset G x z).mp zz
      rcases cover z e with ha|hb|hc
      · rw [ha] at e
        exact (sx e.symm).elim
      · exact mem_insert.mpr (.inl hb)
      · exact mem_insert_of_mem (mem_filter.mpr ⟨hc,e⟩)
    exact (card_le_card sub).trans (card_insert_le _ _)
  by_cases ax : G.Adj a x
  · have nb : ¬G.Adj b x := fun bx=>no ⟨ax,bx⟩
    apply combine (t:=a) nb
    intro z e
    rcases shore_closed C x xc z e with h|h|h
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr h)
  · exact combine ax (shore_closed C x xc)

private theorem rooted_common_shore_of_equal_odd
    (hc : G.Connected) (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D) (four : 4≤(EqualOddShore D).card)
    (cmin : 4≤(Shore C).card) (cmax : (Shore C).card≤8)
    (roots : 2≤(CommonAdjPorts C).card) :
    ∃ s t,G.Adj a s ∧ G.Adj b s ∧ RouteOn G (Shore C) s t := by
  classical
  let S := Shore C
  let U := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let K : Finset U := univ.filter (fun x=>G.Adj a x.val ∧ G.Adj b x.val)
  have kCard : K.card=(CommonAdjPorts C).card := by
    apply card_bij (fun u _=>u.val)
    · intro u h
      exact mem_filter.mpr ⟨u.property,(mem_filter.mp h).2⟩
    · intro u _ v _ e
      exact Subtype.ext e
    · intro u h
      exact ⟨⟨u,(mem_filter.mp h).1⟩,mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2⟩,rfl⟩
  have rootK : 2≤K.card := by rwa [kCard]
  have inside (u : U) : (ArticulationPair.inside G S u.val).card=J.degree u :=
    ArticulationPair.inside_card_eq_degree_induce (G:=G) S u
  have common (u : U) (port : G.Adj a u.val ∧ G.Adj b u.val) : S.card≤J.degree u+2 := by
    let N := ArticulationPair.inside G S u.val
    let Q := S∩DistanceTwo G u.val
    have both := common_port_close_of_equal_odd hc even conn cd four u.property port.1 port.2
    have sub : S⊆insert u.val (N∪Q) := by
      intro w ws
      by_cases e : w=u.val
      · exact mem_insert.mpr (.inl e)
      apply mem_insert_of_mem
      by_cases adj : G.Adj u.val w
      · exact mem_union_left _ (mem_filter.mpr ⟨ws,adj⟩)
      have lo := hc.one_lt_dist_of_ne_of_not_adj (fun h=>e h.symm) adj
      have hi := both.2 w ws
      exact mem_union_right _ (mem_inter.mpr ⟨ws,
        by simp [DistanceTwo,show G.dist u.val w=2 by omega]⟩)
    have sz := (card_le_card sub).trans (card_insert_le u.val (N∪Q))
    have rt := card_union_le N Q
    have q := both.1
    change Q.card≤1 at q
    have ni : N.card=J.degree u := inside u
    omega
  have size : Fintype.card U = S.card := Fintype.card_coe S
  change 4≤S.card at cmin
  change S.card≤8 at cmax
  have pair (u v : U) (hu : 5≤G.degree u.val) (hv : 5≤G.degree v.val) (_ : u≠v) :
      Fintype.card U≤J.degree u+J.degree v := by
    have rule (w : U) (wh : 5≤G.degree w.val) : S.card≤J.degree w+2 ∨ 4≤J.degree w := by
      by_cases hw : G.Adj a w.val ∧ G.Adj b w.val
      · exact .inl (common w hw)
      · have h := global_degree_le_inside_add_one_of_noncommon w.property hw
        rw [inside] at h
        exact .inr (by omega)
    rcases rule u hu with h|h <;> rcases rule v hv with k|k <;> omega
  obtain ⟨r,rK,t,p,pp,ps⟩ := rooted_Ore_with_two_roots (shore_connected C) K rootK
    (fun u=>5≤G.degree u.val)
    (fun u v e=>degree u.val v.val (fun h=>e (Subtype.ext h))) pair
  have ra := (mem_filter.mp rK).2
  exact ⟨r.val,t.val,ra.1,ra.2,lift_side_path S p pp ps⟩

theorem traceable_of_equal_odd_common_ports_two_adjacent_shores
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V}, z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (oc : 4≤(EqualOddShore C).card) (od : 4≤(EqualOddShore D).card)
    (c8 : (Shore C).card≤8) (d8 : (Shore D).card≤8)
    (cp : 2≤(CommonAdjPorts C).card) (dp : 2≤(CommonAdjPorts D).card) :
    ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have c4 := oc.trans (card_le_card (show EqualOddShore C ⊆ Shore C from filter_subset _ _))
  have d4 := od.trans (card_le_card (show EqualOddShore D ⊆ Shore D from filter_subset _ _))
  obtain ⟨s,t,as',_,p⟩ := rooted_common_shore_of_equal_odd hc even conn degree cd od c4 c8 cp
  obtain ⟨u,v,_,bu,q⟩ := rooted_common_shore_of_equal_odd hc even conn degree cd.symm oc d4 d8 dp
  have left := p.reverse.suffix as'.symm (shore_off C).1
  have right := q.prefix bu (shore_off D).2
  have apart : Disjoint (insert a (Shore C)) (insert b (Shore D)) := by
    refine disjoint_left.mpr ?_
    intro z zl zr
    rcases mem_insert.mp zl with rfl|zc
    · exact (by simp [ab.ne,(shore_off D).1] : z∉insert b (Shore D)) zr
    rcases mem_insert.mp zr with rfl|zd
    · exact (shore_off C).2 zc
    · exact disjoint_left.mp (shore_disjoint cd) zc zd
  obtain ⟨w,wp,ws⟩ := left.join right apart ab
  refine ⟨t,v,w,wp,fun z => (ws z).mpr ?_⟩
  by_cases za : z=a
  · simp [za]
  by_cases zb : z=b
  · simp [zb]
  rcases cover za zb with h|h <;> simp [h]

#print axioms traceable_of_equal_odd_common_ports_two_adjacent_shores
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
