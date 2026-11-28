import AdjacentCutFiveComponents189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open scoped BigOperators
open private CutGraph Shore mem_shore shore_off shore_nonempty shore_disjoint shore_closed
  shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private Vis vis_sub vis_card_ge_two foreign_pos_even degree_le_shore_add_one
  degree_le_shore sum_subset_card count_sum positive_cap from AdjacentCutFiveComponents189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem two_visible_shore_of_three_and_singleton (hc : G.Connected) (ab : a≠b)
    (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y)
    (three : Nat.card (CutGraph (G := G) a b).ConnectedComponent = 3)
    (D : (CutGraph (G := G) a b).ConnectedComponent) (singleton : (Shore D).card = 1) :
    ∃ C : (CutGraph (G := G) a b).ConnectedComponent,
      C ≠ D ∧ (Vis C).card = 2 ∧ 5 ≤ (Shore C).card := by
  classical
  let J := CutGraph (G := G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  change Nat.card J.ConnectedComponent = 3 at three
  rw [Nat.card_eq_fintype_card] at three
  let T : Finset J.ConnectedComponent := univ.erase D
  have t2 : T.card = 2 := by simp [T, three]
  obtain ⟨x,dx⟩ := card_eq_one.mp singleton
  obtain ⟨xa,ha,ax⟩ := shore_hit_a ab conn D
  obtain ⟨xb,hb,bx⟩ := shore_hit_b ab conn D
  rw [dx,mem_singleton] at ha hb
  subst xa
  subst xb
  have xD : x ∈ Shore D := by simp [dx]
  have xlo : G.degree x < 5 := by
    have h := degree_le_shore_add_one D xD
    omega
  have high (C : J.ConnectedComponent) (ct : C ∈ T) (y : V) (yc : y ∈ Shore C) :
      5 ≤ G.degree y := by
    have ne : x ≠ y := fun e => disjoint_left.mp (shore_disjoint (mem_erase.mp ct).1) yc (e.symm ▸ xD)
    exact (degree x y ne).resolve_left (by omega)
  have large (C : J.ConnectedComponent) (ct : C∈T) : 4≤(Shore C).card := by
    obtain ⟨y,yc⟩ := shore_nonempty C
    have h := degree_le_shore_add_one C yc
    have h' := high C ct y yc
    omega
  have vis2 (C : J.ConnectedComponent) (ct : C∈T) : 2≤(Vis C).card :=
    vis_card_ge_two ab conn C (by have h:=large C ct; omega)
  have sum : (∑ C∈T,(Vis C).card) ≤ 5 := by
    have h := sum_subset_card T Vis (fun C _=>vis_sub C) (PositiveEven G x) (by
      intro C ct y ym
      have yy := mem_filter.mp ym
      have dc := (mem_erase.mp ct).1.symm
      exact yy.2.elim (foreign_pos_even hc dc xD yy.1 ax)
        (foreign_pos_even hc dc xD yy.1 bx))
    exact h.trans (positive_cap x even)
  have some : ∃ C∈T,(Vis C).card = 2 := by
    by_contra! no
    have cnt : T.card * 3 ≤ ∑ C∈T,(Vis C).card := count_sum T Vis 3 (by
      intro C ct
      have h := no C ct
      have lo := vis2 C ct
      omega)
    exact (Nat.not_le_of_gt (show 5 < T.card * 3 by omega)) (cnt.trans sum)
  obtain ⟨C,ct,c2⟩ := some
  refine ⟨C,(mem_erase.mp ct).1,c2,?_⟩
  by_cases c5 : 5≤(Shore C).card
  · exact c5
  · have all : Shore C ⊆ Vis C := by
      intro y yc
      refine mem_filter.mpr ⟨yc,?_⟩
      by_cases ay : G.Adj a y
      · exact .inl ay
      · have le := degree_le_shore C yc (.inl ay)
        have h := high C ct y yc
        omega
    have le := card_le_card all
    have four := large C ct
    omega

/-- Two visible vertices of a shore with interior are a new actual
separating pair. One new component is contained strictly in the old shore. -/
theorem actual_cut_of_two_visible_shore
    (C : (CutGraph (G := G) a b).ConnectedComponent)
    (ports : (Vis C).card = 2) (large : 2 < (Shore C).card) :
    ∃ u v : V, u ≠ v ∧ Vis C = {u,v} ∧
      2 ≤ Nat.card (CutGraph (G := G) u v).ConnectedComponent ∧
      ∃ E : (CutGraph (G := G) u v).ConnectedComponent,
        Shore E ⊆ (Shore C \ {u,v}) ∧ (Shore E).card < (Shore C).card := by
  classical
  obtain ⟨u,v,uv,e⟩ := card_eq_two.mp ports
  have uvis : u ∈ Vis C := by simp [e]
  have vvis : v ∈ Vis C := by simp [e]
  have uc := vis_sub C uvis
  have vc := vis_sub C vvis
  let U := ({u,v} : Finset V)
  have us : U ⊆ Shore C := by
    intro z hz
    simp only [U,mem_insert,mem_singleton] at hz
    exact hz.elim (fun h=>h.symm ▸ uc) (fun h=>h.symm ▸ vc)
  have u2 : U.card = 2 := by simp [U,uv]
  have dcard := card_sdiff_add_card_eq_card us
  obtain ⟨x,xi⟩ : ((Shore C) \ U).Nonempty := card_pos.mp (by omega)
  have xn := mem_sdiff.mp xi
  have xu : x ≠ u := fun h => xn.2 (by simp [U,h])
  have xv : x ≠ v := fun h => xn.2 (by simp [U,h])
  have au : a ≠ u := fun h => (shore_off C).1 (h.symm ▸ uc)
  have av : a ≠ v := fun h => (shore_off C).1 (h.symm ▸ vc)
  let J := CutGraph (G := G) u v
  let x' : {z : V | z≠u ∧ z≠v} := ⟨x,xu,xv⟩
  let a' : {z : V | z≠u ∧ z≠v} := ⟨a,au,av⟩
  have walk_stays {s t : {z : V | z≠u ∧ z≠v}} (p : J.Walk s t) :
      s.val ∈ Shore C → t.val ∈ Shore C := by
    induction p with
    | nil => exact id
    | @cons s w t sw p ih =>
      intro sc
      have notU : s.val ∉ U := by
        simpa only [U,mem_insert,mem_singleton,not_or] using s.property
      have ee : G.Adj s.val w.val := sw
      apply ih
      rcases shore_closed C s.val sc w.val ee with ea|eb|wc
      · exact (notU (by
          change s.val ∈ ({u,v} : Finset V)
          rw [← e]
          exact mem_filter.mpr ⟨sc,.inl (ea ▸ ee.symm)⟩)).elim
      · exact (notU (by
          change s.val ∈ ({u,v} : Finset V)
          rw [← e]
          exact mem_filter.mpr ⟨sc,.inr (eb ▸ ee.symm)⟩)).elim
      · exact wc
  let E := J.connectedComponentMk x'
  let F := J.connectedComponentMk a'
  have EF : E≠F := by
    intro eq
    obtain ⟨p⟩ := ConnectedComponent.exact eq
    exact (shore_off C).1 (walk_stays p xn.1)
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  have n2 : 2 ≤ Nat.card J.ConnectedComponent := by
    rw [Nat.card_eq_fintype_card]
    have cnt := card_le_univ ({E,F} : Finset J.ConnectedComponent)
    simpa [EF] using cnt
  have sub : Shore E ⊆ (Shore C \ U) := by
    intro z ze
    obtain ⟨zoff,h⟩ := mem_shore.mp ze
    obtain ⟨p⟩ := ConnectedComponent.exact h.symm
    refine mem_sdiff.mpr ⟨walk_stays p xn.1,?_⟩
    simpa only [U,mem_insert,mem_singleton,not_or] using zoff
  have sz := card_le_card sub
  have sl : (Shore E).card < (Shore C).card := by omega
  exact ⟨u,v,uv,e,n2,E,sub,sl⟩

#print axioms two_visible_shore_of_three_and_singleton
#print axioms actual_cut_of_two_visible_shore
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
