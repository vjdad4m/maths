import P5CoreCliqueFibers133
import C7BranchResidualP5Core133
import P9FreeC4FreeRadius133

namespace Graffiti133P5CoreShape
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Camby
  Graffiti133MultiWeighted Graffiti133FiveResidual Graffiti133P5Radius
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000

variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

private theorem radius3_double_dom_universal
    (hc : G.Connected) (D : Finset V) (cd : CD G D)
    (E : Finset (D : Set V)) (ed : CD (G.induce (D : Set V)) E)
    (c : (E : Set (D : Set V)))
    (reach : ∀ x : (E : Set (D : Set V)),c=x ∨
      ((G.induce (D : Set V)).induce (E : Set (D : Set V))).Adj c x) :
    radius G≤3 := by
  classical
  let a := c.val.val
  have near (x : (E : Set (D : Set V))) : G.dist a x.val.val≤1 := by
    rcases reach x with eq|e
    · rw [←eq]
      change G.dist a a≤1
      rw [dist_self]
      decide
    · rw [dist_eq_one_iff_adj.mpr (show G.Adj a x.val.val from e)]
  have d2 (x : (D : Set V)) : G.dist a x.val≤2 := by
    rcases ed.2 x with xe|⟨y,ye,xy⟩
    · have h : G.dist a x.val≤1 := near ⟨x,xe⟩
      omega
    · have h : G.dist a x.val≤G.dist a y.val+G.dist y.val x.val := hc.dist_triangle
      rw [dist_eq_one_iff_adj.mpr (show G.Adj y.val x.val from xy.symm)] at h
      have yb : G.dist a y.val≤1 := near ⟨y,ye⟩
      omega
  have all (x : V) : G.dist a x≤3 := by
    rcases cd.2 x with xd|⟨y,yd,xy⟩
    · have h : G.dist a x≤2 := d2 ⟨x,xd⟩
      omega
    · have h : G.dist a x≤G.dist a y+G.dist y x := hc.dist_triangle
      rw [dist_eq_one_iff_adj.mpr xy.symm] at h
      have yb : G.dist a y≤2 := d2 ⟨y,yd⟩
      omega
  unfold radius
  have hm : Finset.univ.sup (G.dist a) ∈ Finset.univ.image (fun u => Finset.univ.sup (G.dist u)) :=
    Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have hl := Finset.min_le hm
  cases e : (Finset.univ.image (fun u => Finset.univ.sup (G.dist u))).min with
  | top => exact Nat.zero_le _
  | coe d =>
    have hu : d≤Finset.univ.sup (G.dist a) := by simpa [e] using hl
    exact hu.trans (Finset.sup_le_iff.mpr (fun w _=>all w))

def InnerProfile {W : Type*} (J : SimpleGraph W) (A : Finset W) : Prop :=
  CD J A ∧ J.IsClique (A : Set W) ∧ UniqueAnchor J A ∧ 2≤A.card ∧
    ∀ x y z, x∉A → y∉A → z∉A → J.Adj x y → J.Adj x z → y=z

theorem radius_four_residual_inner_shape
    (hc : G.Connected) (h4 : FourCycleFree G) (h9 : NoPath G 9) (r : 4≤radius G)
    (high : 4*Fintype.card V<∑ x : V,localIndependence G x) :
    radius G=4 ∧
    ∃ D : Finset V,MinimalSize G D ∧ NoPath (G.induce (D : Set V)) 7 ∧
      ∃ E : Finset (D : Set V),MinimalSize (G.induce (D : Set V)) E ∧
        let J := (G.induce (D : Set V)).induce (E : Set (D : Set V))
        NoPath J 5 ∧
        ((∃ H : Hole J 5, Function.Surjective H.c) ∨ ∃ A : Finset (E : Set (D : Set V)), InnerProfile J A) := by
  classical
  have rlim := no_induced_P9_C4free_radius_at_most_four hc h4 h9
  refine ⟨by omega,?_⟩
  obtain ⟨D,dm,d7,E,em,e5⟩ := if_radius_four_and_high_mean_nested_p5_free_core hc h4 h9 r high
  refine ⟨D,dm,d7,E,em,e5,?_⟩
  let J := (G.induce (D : Set V)).induce (E : Set (D : Set V))
  rcases p5free_C4free_core_shape em.1.1 (restricted_c4 (restricted_c4 h4 D) E) e5 with five|⟨A,cd,cl,un,hm⟩
  · exact Or.inl five
  have h2 : 2≤A.card := by
    by_contra! sm
    obtain ⟨a⟩ := cd.1.nonempty
    have pos : 0<A.card := Finset.card_pos.mpr ⟨a.val,a.property⟩
    have ca : A={a.val} := by
      have e : A.card=1 := by omega
      have sa : ({a.val} : Finset (E : Set (D : Set V)))⊆A :=
        Finset.singleton_subset_iff.mpr a.property
      exact (Finset.eq_of_subset_of_card_le sa (by rw [e,Finset.card_singleton])).symm
    have universal (x : (E : Set (D : Set V))) : a.val=x ∨ J.Adj a.val x := by
      rcases cd.2 x with h|⟨y,ym,xy⟩
      · left
        rw [ca,Finset.mem_singleton] at h
        exact h.symm
      · right
        rw [ca,Finset.mem_singleton] at ym
        exact ym ▸ xy.symm
    have contra := radius3_double_dom_universal hc D dm.1 E em.1 a.val universal
    omega
  exact Or.inr ⟨A,cd,cl,un,h2,hm⟩

#print axioms radius_four_residual_inner_shape
end Graffiti133P5CoreShape
