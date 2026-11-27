import ArticulationEightLift189
namespace Graffiti189LongestPath.CrossSaturation.ArticulationPair
open SimpleGraph SimpleGraph.Walk Finset
open private left_boundary' right_boundary' from ArticulationEight189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {c : V} (S : Graffiti189LongestPath.CrossSaturation.ArticulationPair G c)
set_option linter.unusedSectionVars false

theorem left_degree_preserved (z : V) (zl : z∈S.L) :
    (G.induce (↑(insert c S.L) : Set V)).degree ⟨z,mem_insert_of_mem zl⟩ = G.degree z := by
  classical
  rw [←inside_card_eq_degree_induce]
  have e : inside G (insert c S.L) z = G.neighborFinset z := by
    ext y
    constructor
    · intro h
      exact (mem_neighborFinset G z y).mpr (mem_filter.mp h).2
    intro h
    have e := (mem_neighborFinset G z y).mp h
    exact mem_filter.mpr ⟨mem_insert.mpr (left_boundary' S zl e),e⟩
  rw [e,card_neighborFinset_eq_degree]

private theorem three_distinct_components {U : Type*} (J : SimpleGraph U) [Fintype U]
    (u v w : U) (uv : ¬J.Reachable u v) (uw : ¬J.Reachable u w) (vw : ¬J.Reachable v w) :
    3≤Nat.card J.ConnectedComponent := by
  classical
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun x=>x.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  let f : Fin 3 → J.ConnectedComponent := ![J.connectedComponentMk u,J.connectedComponentMk v,J.connectedComponentMk w]
  have inj : Function.Injective f := by
    intro i j e
    fin_cases i <;> fin_cases j
    all_goals try rfl
    · exact (uv (ConnectedComponent.exact e)).elim
    · exact (uw (ConnectedComponent.exact e)).elim
    · exact (uv (ConnectedComponent.exact e.symm)).elim
    · exact (vw (ConnectedComponent.exact e)).elim
    · exact (uw (ConnectedComponent.exact e.symm)).elim
    · exact (vw (ConnectedComponent.exact e.symm)).elim
  have h := Fintype.card_le_of_injective f inj
  rw [Fintype.card_fin,←Nat.card_eq_fintype_card] at h
  exact h

/-- If a side contains at least three vertices, a nonporter z and the
articulation cannot have the same sole neighbor in that side. -/
theorem distinct_root_and_outlier_ports (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card≤5)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {z : V} (zl : z∈S.L) (cz : ¬G.Adj c z) (three : 3≤S.L.card) :
    ∃ u∈S.L, ∃ v∈S.L, u≠v ∧ G.Adj c u ∧ G.Adj z v := by
  classical
  obtain ⟨r,rl,cr⟩ := S.hitL
  have zv : ∃ v∈S.L,G.Adj z v := by
    obtain ⟨q⟩ := hc.preconnected z c
    cases q with
    | nil => exact (S.offL zl).elim
    | cons zv p =>
      rcases left_boundary' S zl zv with h|vl
      · exact (cz (h ▸ zv.symm)).elim
      · exact ⟨_,vl,zv⟩
  obtain ⟨v,vl,zv⟩ := zv
  apply Classical.byContradiction
  intro bad
  have eq : v=r := by
    apply Classical.byContradiction
    intro ne
    exact bad ⟨r,rl,v,vl,Ne.symm ne,cr,zv⟩
  subst v
  have soleC (u : V) (ul : u∈S.L) (cu : G.Adj c u) : u=r := by
    apply Classical.byContradiction
    intro ne
    exact bad ⟨u,ul,r,rl,ne,cu,zv⟩
  have soleZ (u : V) (zu : G.Adj z u) : u=r := by
    rcases left_boundary' S zl zu with h|ul
    · exact (cz (h ▸ zu.symm)).elim
    · apply Classical.byContradiction
      intro ne
      exact bad ⟨r,rl,u,ul,Ne.symm ne,cr,zu⟩
  have w_exists : ∃ w∈S.L,w≠z ∧ w≠r := by
    apply Classical.byContradiction
    intro no
    have sub : S.L ⊆ ({z,r} : Finset V) := by
      intro w wl
      by_cases ez : w=z
      · simp [ez]
      by_cases er : w=r
      · simp [er]
      exact (no ⟨w,wl,ez,er⟩).elim
    have h := card_le_card sub
    have b := card_insert_le z ({r} : Finset V)
    simp at b
    omega
  obtain ⟨w,wl,wz,wr⟩ := w_exists
  let T : Set V := {u | u≠r}
  let J := G.induce T
  let cc : T := ⟨c,cr.ne⟩
  let zz : T := ⟨z,zv.ne⟩
  let ww : T := ⟨w,wr⟩
  let A := insert c S.R
  have stay {u v : T} (p : J.Walk u v) :
      u.val∈A → v.val∈A := by
    induction p with
    | nil => exact id
    | @cons u y v uy q ih =>
      intro ua
      apply ih
      change G.Adj u.val y.val at uy
      rcases mem_insert.mp ua with uC|ur
      · have cy : G.Adj c y.val := uC ▸ uy
        rcases S.cover y.val with h|yl|yr
        · exact (cy.ne h.symm).elim
        · exact (y.property (soleC _ yl cy)).elim
        · exact mem_insert_of_mem yr
      · rcases right_boundary' S ur uy with h|yr
        · exact mem_insert.mpr (.inl h)
        · exact mem_insert_of_mem yr
  have zno (u : T) (uz : u.val≠z) : ¬J.Reachable zz u := by
    rintro ⟨p⟩
    have first {j k : T} (q : J.Walk j k) (jz : j.val=z) : k.val=z := by
      cases q with
      | nil => exact jz
      | @cons j v k jv q =>
        have e : G.Adj j.val v.val := jv
        exact (v.property (soleZ _ (jz ▸ e))).elim
    exact uz (first p rfl)
  have za : z≠c := fun e=>S.offL (e ▸ zl)
  have wa : w∉A := by
    intro h
    rcases mem_insert.mp h with e|wr'
    · exact S.offL (e ▸ wl)
    · exact disjoint_left.mp S.dis wl wr'
  have noCW : ¬J.Reachable cc ww := by
    rintro ⟨p⟩
    exact wa (stay p (mem_insert_self _ _))
  have threeC := three_distinct_components J zz cc ww (zno cc za.symm) (zno ww wz) noCW
  have cap := component_card_le_two_at_articulation hc r even degree
  change Nat.card J.ConnectedComponent≤2 at cap
  omega


theorem left_size_ge_four_of_two
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (two : 2≤S.L.card) : 4≤S.L.card := by
  classical
  obtain ⟨v,vl,w,wl,vw⟩ := one_lt_card.mp (by omega : 1<S.L.card)
  have le (x : V) (xl : x∈S.L) : G.degree x≤S.L.card := by
    have sub : G.neighborFinset x ⊆ insert c (S.L.erase x) := by
      intro z hz
      have e := (mem_neighborFinset G x z).mp hz
      rcases left_boundary' S xl e with rfl|zl
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_erase.mpr ⟨e.ne.symm,zl⟩)
    have n := card_le_card sub
    rw [card_neighborFinset_eq_degree] at n
    have b := card_insert_le c (S.L.erase x)
    rw [card_erase_of_mem xl] at b
    omega
  rcases degree _ _ vw with v4|w4
  · exact v4.trans (le v vl)
  · exact w4.trans (le w wl)

/-- A spanning path of the side plus articulation, rooted at the
articulation, lifts directly to a rooted path in the ambient graph. -/
theorem lift_rooted_with_articulation
    (rooted : ∃ y,∃ p : (G.induce (↑(insert c S.L) : Set V)).Walk
      ⟨c,mem_insert_self _ _⟩ y,p.IsPath ∧ ∀ z,z∈p.support) :
    ∃ z,∃ q : G.Walk c z,q.IsPath ∧ ∀ u,u∈q.support ↔ u=c ∨ u∈S.L := by
  classical
  obtain ⟨z,p,pp,ps⟩ := rooted
  let f : (G.induce (↑(insert c S.L) : Set V)) →g G := {toFun := Subtype.val, map_rel' := fun h=>h}
  let q := p.map f
  have qs (u : V) : u∈q.support ↔ u∈insert c S.L := by
    change u∈(p.map f).support ↔ _
    rw [support_map,List.mem_map]
    constructor
    · rintro ⟨w,_,rfl⟩
      exact w.property
    · intro uL
      exact ⟨⟨u,uL⟩,ps _,rfl⟩
  have qp : q.IsPath := by
    rw [isPath_def]
    change (p.map f).support.Nodup
    rw [support_map]
    exact pp.support_nodup.map Subtype.val_injective
  exact ⟨z.val,q,qp,fun u => (qs u).trans mem_insert⟩

#print axioms left_size_ge_four_of_two
#print axioms lift_rooted_with_articulation
#print axioms left_degree_preserved
#print axioms distinct_root_and_outlier_ports
end Graffiti189LongestPath.CrossSaturation.ArticulationPair
