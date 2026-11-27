import P5NestedC7Radius133
import C9Main133

namespace Graffiti133P5Radius
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Camby
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

private theorem radiusUpper9 (a : V) (n : Nat) (bound : ∀ x,G.dist a x≤n) : radius G≤n := by
  classical
  unfold radius
  have hm : Finset.univ.sup (G.dist a) ∈ Finset.univ.image (fun u => Finset.univ.sup (G.dist u)) :=
    Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have hl := Finset.min_le hm
  cases e : (Finset.univ.image (fun u => Finset.univ.sup (G.dist u))).min with
  | top => exact Nat.zero_le _
  | coe d =>
    have hu : d≤Finset.univ.sup (G.dist a) := by simpa [e] using hl
    exact hu.trans (Finset.sup_le_iff.mpr (fun w _=>bound w))

private theorem distTwo9 (hc : G.Connected) {a b c : V} (ab : G.Adj a b) (bc : G.Adj b c) :
    G.dist a c≤2 := by
  have d : G.dist a c≤G.dist a b+G.dist b c := hc.dist_triangle
  rw [dist_eq_one_iff_adj.mpr ab,dist_eq_one_iff_adj.mpr bc] at d
  exact d

def NearTwo9 (i : Fin 9) : Prop :=
  i=0 ∨ Cyclic 0 i ∨ ∃ j : Fin 9,Cyclic 0 j ∧ Cyclic j i

instance (i : Fin 9) : Decidable (NearTwo9 i) := by unfold NearTwo9; infer_instance

def NearThree9 (i : Fin 9) : Prop :=
  NearTwo9 i ∨ ∃ j : Fin 9,NearTwo9 j ∧ Cyclic j i

instance (i : Fin 9) : Decidable (NearThree9 i) := by unfold NearThree9; infer_instance

theorem nine_reachable_from_zero :
    ∀ i : Fin 9,NearThree9 i ∨ ∃ j : Fin 9,NearThree9 j ∧ Cyclic j i := by decide

theorem profile_nine_near_zero :
    ∀ p : Fin 57,∃ i∈Graffiti133C9.profileContacts p,NearThree9 i := by decide

theorem dominating_nine_radius_four (H : Hole G 9) (hc : G.Connected)
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (dom : ∀ x,Outside H.c x→∃ i,G.Adj x (H.c i)) : radius G≤4 := by
  have d2 (i : Fin 9) (near : NearTwo9 i) : G.dist (H.c 0) (H.c i)≤2 := by
    rcases near with rfl|ed|⟨j,ab,bc⟩
    · rw [dist_self]
      decide
    · rw [dist_eq_one_iff_adj.mpr ((H.adj _ _).mpr ed)]
      decide
    · exact distTwo9 hc ((H.adj _ _).mpr ab) ((H.adj _ _).mpr bc)
  have d3 (i : Fin 9) (near : NearThree9 i) : G.dist (H.c 0) (H.c i)≤3 := by
    rcases near with q|⟨j,q,ed⟩
    · exact (d2 _ q).trans (by decide)
    · have d : G.dist (H.c 0) (H.c i)≤G.dist (H.c 0) (H.c j)+G.dist (H.c j) (H.c i) :=
        hc.dist_triangle
      rw [dist_eq_one_iff_adj.mpr ((H.adj _ _).mpr ed)] at d
      have := d2 j q
      omega
  apply radiusUpper9 (H.c 0) 4
  intro x
  have move {j : Fin 9} {x : V} (q : NearThree9 j) (e : G.Adj (H.c j) x) :
      G.dist (H.c 0) x≤4 := by
    have d : G.dist (H.c 0) x≤G.dist (H.c 0) (H.c j)+G.dist (H.c j) x := hc.dist_triangle
    rw [dist_eq_one_iff_adj.mpr e] at d
    have := d3 j q
    omega
  by_cases off : Outside H.c x
  · obtain ⟨p,px⟩ := Graffiti133C9.classify_profile H h4 h9 x off (dom x off)
    obtain ⟨i,im,near⟩ := profile_nine_near_zero p
    exact move near ((px i).mpr im).symm
  · unfold Outside at off
    push_neg at off
    obtain ⟨i,h⟩ := off
    subst x
    rcases nine_reachable_from_zero i with near|⟨j,near,ji⟩
    · exact (d3 i near).trans (by decide)
    · exact move near ((H.adj _ _).mpr ji)

theorem no_induced_P9_C4free_radius_at_most_four
    (hc : G.Connected) (h4 : FourCycleFree G) (h9 : NoPath G 9) : radius G≤4 := by
  apply Classical.byContradiction
  intro hi
  have r : 5≤radius G := by omega
  obtain ⟨H,dom⟩ := radius_five_has_dominating_C9 hc h4 h9 r
  exact hi (dominating_nine_radius_four H hc h4 h9 dom)

#print axioms dominating_nine_radius_four
#print axioms no_induced_P9_C4free_radius_at_most_four
end Graffiti133P5Radius
