import AdjacentCutFiveTwinBothFour189
import RootedOreTwoRootsNonedge189
import AdjacentCutFiveMetric189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore shore_closed shore_off shore_connected shore_disjoint shore_hit_a from AdjacentCutFiveActual189
open private Vis vis_card_ge_two positive_cap degree_le_shore_add_one from AdjacentCutFiveComponents189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
open private mem_positive d2 from AdjacentCutFiveBound189
open private lift_side_path from DegreeFiveSmallSides189
open private twin_partition twin_even_budget glue_twin_shore_routes twin_shore_root_of_near twin_port_close from AdjacentCutFiveTwinBothFour189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem local_second_lower_of_far
    (hc : G.Connected)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    {C : Cmp G a b} {x z : V} (_xC : x∈Shore C) (ax : G.Adj a x) (bx : G.Adj b x)
    (zL : z∈Shore C) (d3 : 3≤G.dist x z) :
    2≤((Shore C)∩DistanceTwo G x).card := by
  classical
  let Q := (Shore C)∩DistanceTwo G x
  by_cases size : 2≤Q.card
  · exact size
  have fewer : Q.card<2 := Nat.lt_of_not_ge size
  exfalso
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
  have c := conn Q fewer
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



private theorem global_degree_le_inside_add_two {C : Cmp G a b}
    {u : V} (uc : u∈Shore C) :
    G.degree u ≤ (ArticulationPair.inside G (Shore C) u).card+2 := by
  classical
  let P := ArticulationPair.inside G (Shore C) u
  have sub : G.neighborFinset u ⊆ insert a (insert b P) := by
    intro w hw
    have e := (mem_neighborFinset G u w).mp hw
    rcases shore_closed C u uc w e with rfl|rfl|wc
    · simp
    · simp
    · exact mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨wc,e⟩))
  have h := card_le_card sub
  rw [card_neighborFinset_eq_degree] at h
  have h1 := card_insert_le a (insert b P)
  have h2 := card_insert_le b P
  change G.degree u≤P.card+2
  omega

private theorem global_degree_le_inside_if_dark {C : Cmp G a b}
    {u : V} (uc : u∈Shore C) (na : ¬G.Adj a u) (nb : ¬G.Adj b u) :
    G.degree u ≤ (ArticulationPair.inside G (Shore C) u).card := by
  classical
  have sub : G.neighborFinset u ⊆ ArticulationPair.inside G (Shore C) u := by
    intro w hw
    have e := (mem_neighborFinset G u w).mp hw
    rcases shore_closed C u uc w e with rfl|rfl|wc
    · exact (na e.symm).elim
    · exact (nb e.symm).elim
    · exact mem_filter.mpr ⟨wc,e⟩
  exact card_le_card sub

private theorem twin_shore_root_from_ore
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    (twin : ∀ z, z≠a → z≠b → (G.Adj a z ↔ G.Adj b z))
    (ab : a ≠ b)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    {C : Cmp G a b} (two : 2≤(Shore C).card)
    (ore : ∀ u∈Shore C, ∀ v∈Shore C, u≠v → ¬G.Adj u v →
      5≤G.degree u → 5≤G.degree v →
      (Shore C).card≤(ArticulationPair.inside G (Shore C) u).card+
        (ArticulationPair.inside G (Shore C) v).card) :
    ∃ s t,G.Adj a s ∧ RouteOn G (Shore C) s t := by
  classical
  let S := Shore C
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
  have roots : 2≤K.card := by rw [eqK]; exact vis_card_ge_two ab conn C two
  have pair (u v : U) (hu : 5≤G.degree u.val) (hv : 5≤G.degree v.val) (n : u≠v) (no : ¬J.Adj u v) :
      Fintype.card U≤J.degree u+J.degree v := by
    have sc : Fintype.card U = S.card := Fintype.card_coe S
    rw [sc,←ArticulationPair.inside_card_eq_degree_induce (G:=G) S u,
      ←ArticulationPair.inside_card_eq_degree_induce (G:=G) S v]
    exact ore u.val u.property v.val v.property (fun e=>n (Subtype.ext e)) no hu hv
  obtain ⟨r,rK,t,p,pp,ps⟩ := rooted_Ore_with_two_roots_of_nonedge (shore_connected C) K roots
    (fun u=>5≤G.degree u.val)
    (fun u v e=>degree u.val v.val (fun h=>e (Subtype.ext h))) pair
  exact ⟨r.val,t.val,(mem_filter.mp rK).2,lift_side_path S p pp ps⟩

private theorem degree_two_from_one_deletion
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    {u v : V} (uv : u≠v) (no : ¬G.Adj u v) : 2≤G.degree u := by
  classical
  by_contra h
  let N := G.neighborFinset u
  have cap : N.card<2 := Nat.lt_of_not_ge h
  let T := (↑N : Set V)ᶜ
  have uh : u∈T := fun e=>G.loopless _ ((mem_neighborFinset G u u).mp e)
  have vh : v∈T := fun e=>no ((mem_neighborFinset G u v).mp e)
  obtain ⟨q⟩ := (conn N cap).preconnected (⟨u,uh⟩ : T) ⟨v,vh⟩
  have ne : (⟨u,uh⟩ : T) ≠ ⟨v,vh⟩ := fun e=>uv (congrArg Subtype.val e)
  cases q with
  | nil => exact ne rfl
  | @cons _ w _ e q =>
    exact w.property ((mem_neighborFinset G u w.val).mpr e)

private theorem local_second_upper
    (hc : G.Connected) (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (twin : ∀ z, z≠a → z≠b → (G.Adj a z ↔ G.Adj b z))
    {C D : Cmp G a b} (cd : C≠D) (three : 3≤(AdjTwinOdd D).card)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) :
    ((Shore C)∩DistanceTwo G x).card≤2 := by
  classical
  let Q := (Shore C)∩DistanceTwo G x
  have sq : Q ⊆ PositiveEven G x := by
    intro z hz
    have d : G.dist x z = 2 := by simpa [DistanceTwo] using (mem_inter.mp hz).2
    exact mem_positive.mpr ⟨fun e=>by rw [e,dist_self] at d; omega,by simp [d]⟩
  have sf := adj_twin_odd_foreign hc twin cd xc ax
  have dis : Disjoint Q (AdjTwinOdd D) :=
    (shore_disjoint cd).mono inter_subset_left (filter_subset _ _)
  have cnt := card_le_card (union_subset sq sf)
  rw [card_union_of_disjoint dis] at cnt
  have c := positive_cap x even
  change Q.card≤2
  omega


private noncomputable def twin_far_set (C : Cmp G a b) (x : V) : Finset V :=
  (Shore C).filter (fun v=>3≤G.dist x v)

private theorem local_far_neighbor
    (hc : G.Connected) {C : Cmp G a b} {x f w : V}
    (ax : G.Adj a x) (bx : G.Adj b x) (ff : f∈twin_far_set C x)
    (fw : G.Adj f w) :
    w∈(Shore C∩DistanceTwo G x) ∨ w∈twin_far_set C x := by
  classical
  obtain ⟨fc,fd⟩ := mem_filter.mp ff
  have h := hc.dist_triangle (u:=x) (v:=w) (w:=f)
  rw [dist_eq_one_iff_adj.mpr fw.symm] at h
  rcases shore_closed C f fc w fw with ha|hb|wc
  · rw [ha,dist_eq_one_iff_adj.mpr ax.symm] at h
    omega
  · rw [hb,dist_eq_one_iff_adj.mpr bx.symm] at h
    omega
  have k : 2≤G.dist x w := by omega
  by_cases e : G.dist x w=2
  · exact .inl (mem_inter.mpr ⟨wc,by simp [DistanceTwo,e]⟩)
  · exact .inr (mem_filter.mpr ⟨wc,by omega⟩)

private theorem high_port_three_foreign_geometry
    (hc : G.Connected) (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (twin : ∀ z, z≠a → z≠b → (G.Adj a z ↔ G.Adj b z))
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D) (three : 3≤(AdjTwinOdd D).card)
    (size : (Shore C).card≤8)
    {x : V} (xc : x∈Shore C) (ax : G.Adj a x) (hx : 5≤G.degree x) :
    let N := ArticulationPair.inside G (Shore C) x
    let Q := Shore C ∩ DistanceTwo G x
    let F := twin_far_set C x
    3≤N.card ∧ (Shore C).card≤N.card+4 ∧
      (F.Nonempty → F.card=1 ∧ Q.card=2 ∧ ∀ v∈F,G.degree v<5) ∧
      (F.card=0 → (Shore C).card≤N.card+3) := by
  classical
  dsimp only
  let N := ArticulationPair.inside G (Shore C) x
  let Q := Shore C∩DistanceTwo G x
  let F := twin_far_set C x
  have bx := (twin x ax.ne.symm (fun e=>(shore_off C).2 (e ▸ xc))).mp ax
  have deg := global_degree_le_inside_add_two xc
  change G.degree x≤N.card+2 at deg
  have n3 : 3≤N.card := by omega
  have q2 : Q.card≤2 := local_second_upper hc even twin cd three xc ax
  have near (v : V) (vn : v∈N) : G.dist x v=1 :=
    dist_eq_one_iff_adj.mpr (mem_filter.mp vn).2
  have second (v : V) (vq : v∈Q) : G.dist x v=2 := by
    simpa [DistanceTwo] using (mem_inter.mp vq).2
  have far (v : V) (vf : v∈F) : 3≤G.dist x v := (mem_filter.mp vf).2
  have of_c (v : V) (h : v∈N∪Q∪F) : v∈(Shore C).erase x := by
    rcases mem_union.mp h with h|h
    · rcases mem_union.mp h with vn|vq
      · have d := near v vn
        exact mem_erase.mpr ⟨fun e=>by rw [e,dist_self] at d; omega,(mem_filter.mp vn).1⟩
      · have d := second v vq
        exact mem_erase.mpr ⟨fun e=>by rw [e,dist_self] at d; omega,(mem_inter.mp vq).1⟩
    · have d := far v h
      exact mem_erase.mpr ⟨fun e=>by rw [e,dist_self] at d; omega,(mem_filter.mp h).1⟩
  have nn : Disjoint N Q := disjoint_left.mpr (fun v vn vq=>by
    have a1 := near v vn
    have a2 := second v vq
    omega)
  have nf : Disjoint (N∪Q) F := disjoint_left.mpr (fun v vU fv=>by
    have a3 := far v fv
    rcases mem_union.mp vU with vn|vq
    · have a1 := near v vn
      omega
    · have a2 := second v vq
      omega)
  have sum := card_le_card of_c
  rw [card_union_of_disjoint nf,card_union_of_disjoint nn, card_erase_of_mem xc] at sum
  have cover : Shore C ⊆ insert x (N∪Q∪F) := by
    intro v vc
    by_cases ex : v=x
    · exact mem_insert.mpr (.inl ex)
    apply mem_insert_of_mem
    by_cases xv : G.Adj x v
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨vc,xv⟩))
    have lo := hc.one_lt_dist_of_ne_of_not_adj (fun h=>ex h.symm) xv
    by_cases d : G.dist x v=2
    · exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨vc,by simp [DistanceTwo,d]⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨vc,by omega⟩)
  have coverSz := (card_le_card cover).trans (card_insert_le x (N∪Q∪F))
  rw [card_union_of_disjoint nf,card_union_of_disjoint nn] at coverSz
  have fcase : F.Nonempty → F.card=1 ∧ Q.card=2 ∧ ∀ v∈F,G.degree v<5 := by
    rintro ⟨z,zf⟩
    have c := local_second_lower_of_far hc conn xc ax bx (mem_filter.mp zf).1 (far z zf)
    change 2≤Q.card at c
    have pos : 0<F.card := card_pos.mpr ⟨z,zf⟩
    have flo (v : V) (vf : v∈F) : G.degree v<5 := by
      have s : G.neighborFinset v ⊆ Q∪F.erase v := by
        intro u un
        have adj := (mem_neighborFinset G v u).mp un
        rcases local_far_neighbor hc ax bx vf adj with uq|uf
        · exact mem_union_left _ uq
        · exact mem_union_right _ (mem_erase.mpr ⟨adj.ne.symm,uf⟩)
      have cnt := (card_le_card s).trans (card_union_le Q (F.erase v))
      rw [card_neighborFinset_eq_degree,card_erase_of_mem vf] at cnt
      omega
    have fc : F.card≤1 := by
      apply Finset.card_le_one.mpr
      intro u uf v vf
      by_contra ne
      rcases degree u v ne with h|h
      · exact (Nat.not_le_of_gt (flo u uf)) h
      · exact (Nat.not_le_of_gt (flo v vf)) h
    exact ⟨by omega,by omega,flo⟩
  have fb : F.card≤1 := by
    by_cases empty : F.Nonempty
    · exact (fcase empty).1.le
    · have e := not_nonempty_iff_eq_empty.mp empty
      simp [e]
  change 3≤N.card ∧ (Shore C).card≤N.card+4 ∧
    (F.Nonempty → F.card=1 ∧ Q.card=2 ∧ ∀ v∈F,G.degree v<5) ∧
    (F.card=0 → (Shore C).card≤N.card+3)
  exact ⟨n3,by omega,fcase,fun h=>by omega⟩


private theorem twin_shore_root_of_three_foreign (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (twin : ∀ z, z≠a → z≠b → (G.Adj a z ↔ G.Adj b z))
    (ab : a ≠ b)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D) (three : 3≤(AdjTwinOdd D).card)
    (min : 6≤(Shore C).card) (max : (Shore C).card≤8) :
    ∃ s t,G.Adj a s ∧ RouteOn G (Shore C) s t := by
  classical
  apply twin_shore_root_from_ore degree twin ab conn (show 2≤(Shore C).card by omega)
  intro u uc v vc uv no hu hv
  let N (w : V) := ArticulationPair.inside G (Shore C) w
  change (Shore C).card≤(N u).card+(N v).card
  have Nu : 3≤(N u).card := by have h := global_degree_le_inside_add_two uc; change G.degree u≤(N u).card+2 at h; omega
  have Nv : 3≤(N v).card := by have h := global_degree_le_inside_add_two vc; change G.degree v≤(N v).card+2 at h; omega
  have largeDark {w : V} (wc : w∈Shore C) (high : 5≤G.degree w)
      (na : ¬G.Adj a w) : 5≤(N w).card := by
    have wa : w≠a := fun e=>(shore_off C).1 (e ▸ wc)
    exact high.trans (global_degree_le_inside_if_dark wc na (fun e=>na ((twin w wa e.ne.symm).mpr e)))
  by_cases au : G.Adj a u
  · by_cases av : G.Adj a v
    · have Pu := high_port_three_foreign_geometry hc even twin conn degree cd three max uc au hu
      have Pv := high_port_three_foreign_geometry hc even twin conn degree cd three max vc av hv
      change _ ∧ (Shore C).card ≤ (N u).card+4 ∧ _ at Pu
      change _ ∧ (Shore C).card ≤ (N v).card+4 ∧ _ at Pv
      by_contra bad
      have sz : (Shore C).card=7 := by have h := Pu.2.1; have k := Pv.2.1; omega
      have ud : (N u).card=3 := by omega
      have vd : (N v).card=3 := by omega
      have uf : (twin_far_set C u).Nonempty := by
        apply card_pos.mp
        by_contra hn
        have e : (twin_far_set C u).card=0 := by omega
        have k : (Shore C).card≤(N u).card+3 := Pu.2.2.2 e
        omega
      have vf : (twin_far_set C v).Nonempty := by
        apply card_pos.mp
        by_contra hn
        have e : (twin_far_set C v).card=0 := by omega
        have k : (Shore C).card≤(N v).card+3 := Pv.2.2.2 e
        omega
      obtain ⟨z,zu⟩ := uf
      obtain ⟨t,tv⟩ := vf
      have ulo := Pu.2.2.1 ⟨z,zu⟩
      have vlo := Pv.2.2.1 ⟨t,tv⟩
      have zt : z=t := by
        by_contra h
        rcases degree z t h with ze|te
        · exact (Nat.not_le_of_gt (ulo.2.2 z zu)) ze
        · exact (Nat.not_le_of_gt (vlo.2.2 t tv)) te
      have zv : z∈twin_far_set C v := zt.symm ▸ tv
      let Q := (Shore C)∩DistanceTwo G u
      have vq : v∈Q := mem_inter.mpr ⟨vc,d2 hc uv no au.symm av⟩
      have znv : ¬G.Adj z v := by
        intro ez
        have vv := (mem_filter.mp zv).2
        rw [dist_eq_one_iff_adj.mpr ez.symm] at vv
        omega
      have qu : G.neighborFinset z ⊆ Q.erase v := by
        intro w wm
        have zw := (mem_neighborFinset G z w).mp wm
        have bu := (twin u au.ne.symm (fun e=>(shore_off C).2 (e ▸ uc))).mp au
        rcases local_far_neighbor hc au bu zu zw with wq|wf
        · exact mem_erase.mpr ⟨fun e=>znv (e ▸ zw),wq⟩
        · exact (zw.ne (Finset.card_le_one.mp ulo.1.le z zu w wf)).elim
      have c := card_le_card qu
      rw [card_neighborFinset_eq_degree,card_erase_of_mem vq] at c
      have l := degree_two_from_one_deletion conn (fun e=>by
        have d := (mem_filter.mp zv).2
        rw [e,dist_self] at d
        omega) znv
      have q2 : Q.card=2 := ulo.2.1
      omega
    · have ha := largeDark vc hv av
      omega
  · have ha := largeDark uc hu au
    omega

end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
