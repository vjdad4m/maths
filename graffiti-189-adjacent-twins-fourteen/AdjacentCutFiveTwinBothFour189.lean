import ArticulationEightLift189
import AdjacentCutFiveTwoOrderTwenty189
import RootedOreTwoRoots189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_closed shore_off shore_connected shore_disjoint from AdjacentCutFiveActual189
open private Vis vis_card_ge_two positive_cap from AdjacentCutFiveComponents189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
open private mem_positive from AdjacentCutFiveBound189
open private lift_side_path from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem twin_port_close (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (twin : ∀ z, z≠a → z≠b → (G.Adj a z ↔ G.Adj b z))
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    {C D : Cmp G a b} (cd : C≠D) (four : 4≤(AdjTwinOdd D).card)
    {x : V} (xC : x∈Shore C) (ax : G.Adj a x) :
    ((Shore C)∩DistanceTwo G x).card≤1 ∧ ∀ z∈Shore C,G.dist x z≤2 := by
  classical
  have bx := (twin x ax.ne.symm (fun e=>(shore_off C).2 (e ▸ xC))).mp ax
  let Q := (Shore C) ∩ DistanceTwo G x
  have foreign := adj_twin_odd_foreign hc twin cd xC ax
  have local' : Q ⊆ PositiveEven G x := by
    intro z hz
    have e : G.dist x z = 2 := by simpa [DistanceTwo] using (mem_inter.mp hz).2
    exact mem_positive.mpr ⟨fun h=>by rw [h,dist_self] at e; omega,by simp [e]⟩
  have dis : Disjoint Q (AdjTwinOdd D) :=
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


private theorem twin_shore_root_of_near (hc : G.Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (twin : ∀ z, z≠a → z≠b → (G.Adj a z ↔ G.Adj b z))
    (ab : a ≠ b)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    {C : Cmp G a b} (min : 4≤(Shore C).card) (max : (Shore C).card≤10)
    (near : ∀ x∈Shore C, G.Adj a x →
      ((Shore C)∩DistanceTwo G x).card≤1 ∧ ∀ z∈Shore C,G.dist x z≤2) :
    ∃ s t,G.Adj a s ∧ RouteOn G (Shore C) s t := by
  classical
  let S := Shore C
  change 4≤S.card at min
  change S.card≤10 at max
  let U := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let K : Finset U := univ.filter (fun x=>G.Adj a x.val)
  have E : Vis C = S.filter (G.Adj a) := by
    ext z
    simp only [Vis,mem_filter]
    constructor
    · rintro ⟨zs,az|bz⟩
      · exact ⟨zs,az⟩
      exact ⟨zs,(twin z (fun e=>(shore_off C).1 (e ▸ zs)) bz.ne.symm).mpr bz⟩
    · exact fun h=>⟨h.1,.inl h.2⟩
  have eqK : K.card=(Vis C).card := by
    rw [E]
    apply card_bij (fun u _=>u.val)
    · intro u h
      exact mem_filter.mpr ⟨u.property,(mem_filter.mp h).2⟩
    · intro u hu v hv e
      exact Subtype.ext e
    · intro u h
      exact ⟨⟨u,(mem_filter.mp h).1⟩,mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2⟩,rfl⟩
  have roots : 2≤K.card := by rw [eqK]; exact vis_card_ge_two ab conn C (show 2≤S.card by omega)
  have inside (u : U) : (ArticulationPair.inside G S u.val).card=J.degree u :=
    ArticulationPair.inside_card_eq_degree_induce (G:=G) S u
  have dark (u : U) (nu : ¬G.Adj a u.val) : 5≤G.degree u.val → 5≤J.degree u := by
    intro hu
    have ua : u.val ≠ a := by
      intro he
      apply (shore_off C).1
      exact Eq.mp (congrArg (fun v : V => v∈Shore C) he) u.property
    have nb : ¬G.Adj b u.val := fun e=>nu ((twin _ ua e.ne.symm).mpr e)
    have s : G.neighborFinset u.val ⊆ ArticulationPair.inside G S u.val := by
      intro z hz
      have e := (mem_neighborFinset G _ _).mp hz
      rcases shore_closed C _ u.property _ e with h | h | h
      · subst z; exact (nu e.symm).elim
      · subst z; exact (nb e.symm).elim
      · exact mem_filter.mpr ⟨h,e⟩
    have h := card_le_card s
    rw [card_neighborFinset_eq_degree,inside] at h
    omega
  have light (u : U) (au : G.Adj a u.val) : S.card≤J.degree u+2 := by
    let N := ArticulationPair.inside G S u.val
    let Q := S ∩ DistanceTwo G u.val
    have sub : S⊆insert u.val (N∪Q) := by
      intro w ws
      by_cases e : w=u.val
      · exact mem_insert.mpr (.inl e)
      apply mem_insert_of_mem
      by_cases adj : G.Adj u.val w
      · exact mem_union_left _ (mem_filter.mpr ⟨ws,adj⟩)
      have lo := hc.one_lt_dist_of_ne_of_not_adj (fun h=>e h.symm) adj
      have hi := (near _ u.property au).2 w ws
      exact mem_union_right _ (mem_inter.mpr ⟨ws,
        by simp [DistanceTwo,show G.dist u.val w=2 by omega]⟩)
    have q := (card_le_card sub).trans (card_insert_le _ _)
    have r := card_union_le N Q
    have ne := (near _ u.property au).1
    change Q.card≤1 at ne
    have h : N.card=J.degree u := inside u
    omega
  have size : Fintype.card U = S.card := Fintype.card_coe S
  have pair (u v : U) (hu : 5≤G.degree u.val) (hv : 5≤G.degree v.val) (_ : u≠v) :
      Fintype.card U≤J.degree u+J.degree v := by
    have rule (w : U) (wh : 5≤G.degree w.val) : S.card≤J.degree w+2 ∨ 5≤J.degree w := by
      by_cases aw : G.Adj a w.val
      · exact .inl (light w aw)
      · exact .inr (dark w aw wh)
    rcases rule u hu with h|h <;> rcases rule v hv with k|k <;> omega
  obtain ⟨r,rK,t,p,pp,ps⟩ := rooted_Ore_with_two_roots (shore_connected C) K roots
    (fun u=>5≤G.degree u.val)
    (fun u v e=>degree u.val v.val (fun h=>e (Subtype.ext h))) pair
  exact ⟨r.val,t.val,(mem_filter.mp rK).2,lift_side_path S p pp ps⟩


private theorem twin_partition {C : Cmp G a b} :
    (AdjTwinOdd C).card+(AdjTwinEven C).card = (Shore C).card := by
  classical
  have dis : Disjoint (AdjTwinOdd C) (AdjTwinEven C) :=
    disjoint_left.mpr (fun _ o e=>(mem_filter.mp o).2 (mem_filter.mp e).2)
  rw [←card_union_of_disjoint dis]
  congr 1
  ext z
  simp only [AdjTwinOdd,AdjTwinEven,mem_union,mem_filter]
  constructor
  · exact fun h=>h.elim And.left And.left
  · intro h
    by_cases e : Even (G.dist a z)
    · exact .inr ⟨h,e⟩
    · exact .inl ⟨h,e⟩

private theorem twin_even_budget
    (even : ∀ x, (EvenFrom G x).card ≤ 6)
    {C D : Cmp G a b} (cd : C≠D) :
    (AdjTwinEven C).card+(AdjTwinEven D).card≤5 := by
  classical
  have sub (K : Cmp G a b) : AdjTwinEven K⊆PositiveEven G a := by
    intro z zm
    obtain ⟨zk,ze⟩ := mem_filter.mp zm
    exact mem_positive.mpr ⟨fun e=>(shore_off K).1 (e ▸ zk),ze⟩
  have dis := (shore_disjoint cd).mono
      (show AdjTwinEven C ⊆ Shore C from filter_subset _ _)
      (show AdjTwinEven D ⊆ Shore D from filter_subset _ _)
  have h := (card_le_card (union_subset (sub C) (sub D))).trans (positive_cap a even)
  rwa [card_union_of_disjoint dis] at h

private theorem glue_twin_shore_routes (ab : G.Adj a b)
    (twin : ∀ z, z≠a → z≠b → (G.Adj a z ↔ G.Adj b z))
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V}, z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (lc : ∃ s t,G.Adj a s ∧ RouteOn G (Shore C) s t)
    (rc : ∃ s t,G.Adj a s ∧ RouteOn G (Shore D) s t) :
    ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨s,t,as',p⟩ := lc
  obtain ⟨u,v,au,q⟩ := rc
  have uD : u∈Shore D := by
    obtain ⟨w,_,hs⟩ := q
    exact (hs u).mp w.start_mem_support
  have ub : u≠b := fun h=>(shore_off D).2 (h ▸ uD)
  have bu := (twin u au.ne.symm ub).mp au
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

open private shore_hit_a from AdjacentCutFiveActual189
theorem traceable_of_adjacent_twins_two_odd_four
    (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (twin : ∀ z, z≠a → z≠b → (G.Adj a z ↔ G.Adj b z))
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V}, z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (oc : 4≤(AdjTwinOdd C).card) (od : 4≤(AdjTwinOdd D).card) :
    ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have r {K L : Cmp G a b} (kl : K≠L)
      (k4 : 4≤(AdjTwinOdd K).card) (l4 : 4≤(AdjTwinOdd L).card) :
      ∃ s t,G.Adj a s ∧ RouteOn G (Shore K) s t := by
    obtain ⟨x,xl,ax⟩ := shore_hit_a ab.ne conn L
    have cap := (card_le_card (adj_twin_odd_foreign hc twin kl.symm xl ax)).trans
      (positive_cap x even)
    have ec := twin_even_budget even kl
    have p : (AdjTwinOdd K).card+(AdjTwinEven K).card=(Shore K).card := twin_partition
    exact twin_shore_root_of_near hc degree twin ab.ne conn (by omega) (by omega)
      (fun _ wk aw=>twin_port_close hc even twin conn kl l4 wk aw)
  exact glue_twin_shore_routes ab twin cd cover (r cd oc od) (r cd.symm od oc)

#print axioms traceable_of_adjacent_twins_two_odd_four
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
