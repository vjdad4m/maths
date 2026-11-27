import P5NestedDomRadius133
import C9Main133
import C7CoreOrder133
import C7MultiWeightedGlobal133
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace Graffiti133P5Radius
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Camby Graffiti133C9
  Graffiti133MultiWeighted
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2300000
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

private theorem radiusUpper (a : V) (n : Nat) (bound : ∀ x,G.dist a x≤n) : radius G≤n := by
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

private theorem distTwo (hc : G.Connected) {a b c : V} (ab : G.Adj a b) (bc : G.Adj b c) :
    G.dist a c≤2 := by
  have d : G.dist a c≤G.dist a b+G.dist b c := hc.dist_triangle
  rw [dist_eq_one_iff_adj.mpr ab,dist_eq_one_iff_adj.mpr bc] at d
  exact d

def ArcNear (i : Fin 7) : Prop :=
  i=0 ∨ Cyclic 0 i ∨ ∃ j : Fin 7,Cyclic 0 j ∧ Cyclic j i

instance (i : Fin 7) : Decidable (ArcNear i) := by unfold ArcNear; infer_instance

theorem all_C7_sites_reachable_from_zero :
    ∀ i : Fin 7,ArcNear i ∨ ∃ j : Fin 7,ArcNear j ∧ Cyclic j i := by decide

theorem long_profile_near_zero :
    ∀ p : Fin 14,∃ i∈Graffiti133CoreSeven.profileContacts p,ArcNear i := by decide

theorem radius_at_most_four_of_p7_free_core_dominating_C7
    (hc : G.Connected) (h4 : FourCycleFree G)
    (D : Finset V) (ddom : CD G D) (H : Hole G 7) (cy : ∀ i,H.c i∈D)
    (d7 : NoPath (G.induce (D : Set V)) 7)
    (dom : ∀ x∈D,Outside H.c x→∃ i,G.Adj x (H.c i)) : radius G≤4 := by
  let a := H.c 0
  have small (i : Fin 7) (near : ArcNear i) : G.dist a (H.c i)≤2 := by
    rcases near with rfl|ed|⟨j,ij,jk⟩
    · change G.dist (H.c 0) (H.c 0)≤2
      rw [dist_self]
      decide
    · change G.dist (H.c 0) (H.c i)≤2
      rw [dist_eq_one_iff_adj.mpr ((H.adj _ _).mpr ed)]
      decide
    · exact distTwo hc ((H.adj _ _).mpr ij) ((H.adj _ _).mpr jk)
  have c3 (i : Fin 7) : G.dist a (H.c i)≤3 := by
    rcases all_C7_sites_reachable_from_zero i with near|⟨j,near,ed⟩
    · exact (small _ near).trans (by decide)
    · have d : G.dist a (H.c i)≤G.dist a (H.c j)+G.dist (H.c j) (H.c i) := hc.dist_triangle
      rw [dist_eq_one_iff_adj.mpr ((H.adj _ _).mpr ed)] at d
      have := small j near
      omega
  have ds (x : V) (xd : x∈D) : G.dist a x≤3 := by
    by_cases off : Outside H.c x
    · let B := restrictedHole H D cy
      let X : (D : Set V) := ⟨x,xd⟩
      obtain ⟨p,pr⟩ := Graffiti133CoreSeven.classify_profile B (restricted_c4 h4 D) d7 X
        (show Outside B.c X from fun i e=>off i (congrArg Subtype.val e)) (dom x xd off)
      obtain ⟨i,im,ne⟩ := long_profile_near_zero p
      have xi : G.Adj x (H.c i) := (pr i).mpr im
      have d : G.dist a x≤G.dist a (H.c i)+G.dist (H.c i) x := hc.dist_triangle
      rw [dist_eq_one_iff_adj.mpr xi.symm] at d
      have := small i ne
      omega
    · unfold Outside at off
      push_neg at off
      obtain ⟨i,e⟩ := off
      exact e.symm ▸ c3 i
  apply radiusUpper a 4
  intro x
  rcases ddom.2 x with xd|⟨y,yd,xy⟩
  · exact (ds x xd).trans (by decide)
  · have d : G.dist a x≤G.dist a y+G.dist y x := hc.dist_triangle
    rw [dist_eq_one_iff_adj.mpr xy.symm] at d
    have := ds y yd
    omega

theorem radius_five_has_dominating_C9
    (hc : G.Connected) (h4 : FourCycleFree G)
    (h9 : NoPath G 9) (r : 5≤radius G) :
    ∃ H : Hole G 9,∀ x,Outside H.c x→∃ i,G.Adj x (H.c i) := by
  classical
  rcases connected_domination_decomposition G hc 7 (by decide) h9 with ⟨D,dd,no7⟩|nine
  · let J := G.induce (D : Set V)
    have p7 : NoPath J 7 := by
      rintro ⟨p,hp⟩
      exact no7 ⟨Subtype.val ∘ p,⟨Subtype.val_injective.comp hp.1,hp.2⟩,fun i=>(p i).property⟩
    rcases connected_domination_decomposition J dd.1 5 (by decide) p7 with ⟨E,ed,no5⟩|⟨B,bd⟩
    · have p5 : NoPath (J.induce (E : Set (D : Set V))) 5 := by
        rintro ⟨p,hp⟩
        exact no5 ⟨Subtype.val ∘ p,⟨Subtype.val_injective.comp hp.1,hp.2⟩,fun i=>(p i).property⟩
      have b := radius_at_most_four_of_nested_p5_free hc h4 D dd E ed p5
      omega
    · let H : Hole G 7 := ⟨Subtype.val ∘ B.c,Subtype.val_injective.comp B.inj,B.adj⟩
      have dom (x : V) (xm : x∈D) (xo : Outside H.c x) : ∃ i,G.Adj x (H.c i) :=
        bd ⟨x,xm⟩ (fun i e=>xo i (congrArg Subtype.val e))
      have lr := radius_at_most_four_of_p7_free_core_dominating_C7 hc h4 D dd H
        (fun i=>(B.c i).property) p7 dom
      omega
  · exact nine

theorem radius_at_least_five_no_p9_mean_four
    (hc : G.Connected) (h4 : FourCycleFree G)
    (h9 : NoPath G 9) (r : 5≤radius G) :
    (∑ x : V,localIndependence G x)≤4*Fintype.card V := by
  obtain ⟨H,d⟩ := radius_five_has_dominating_C9 hc h4 h9 r
  exact dominating_nine_budget H h4 h9 d

#print axioms radius_at_most_four_of_p7_free_core_dominating_C7
#print axioms radius_five_has_dominating_C9
#print axioms radius_at_least_five_no_p9_mean_four
end Graffiti133P5Radius
