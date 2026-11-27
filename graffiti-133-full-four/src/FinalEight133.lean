import CambyCycleDecomp133
import DominatingHex133
import DominatingOctagonAllowFive133
import UnroundedBand133

namespace Graffiti133FinalEight
open SimpleGraph Graffiti133 Graffiti133Camby Graffiti133NoFive Graffiti133Revisit Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem center_exists (G : SimpleGraph V) (hc : G.Connected) :
    ∃ v, ∀ x, G.dist v x ≤ radius G := by
  classical
  obtain ⟨v⟩ := hc.nonempty
  let E (x : V) := Finset.univ.sup (G.dist x)
  let A := Finset.univ.image E
  have hA : A.Nonempty := ⟨E v,Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩⟩
  obtain ⟨c,_,he⟩ := Finset.mem_image.mp (Finset.min'_mem A hA)
  have hr : radius G = A.min' hA := by
    unfold radius
    change A.min.getD 0 = _
    rw [← Finset.coe_min' hA]
    rfl
  exact ⟨c,fun x => hr.symm ▸ he ▸ Finset.le_sup (f := G.dist c) (Finset.mem_univ x)⟩

private theorem radius_to (G : SimpleGraph V) (v : V) (k : ℕ) (h : ∀ w,G.dist v w≤k) :
    radius G ≤ k := by
  classical
  unfold radius
  have hm : Finset.univ.sup (G.dist v) ∈ Finset.univ.image (fun u => Finset.univ.sup (G.dist u)) :=
    Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  have hl := Finset.min_le hm
  cases e : (Finset.univ.image (fun u => Finset.univ.sup (G.dist u))).min with
  | top => exact Nat.zero_le _
  | coe d =>
    have hu : d ≤ Finset.univ.sup (G.dist v) := by simpa [e] using hl
    exact hu.trans (Finset.sup_le_iff.mpr (fun w _ => h w))

private theorem radius_of_cd [DecidableEq V] (hc : G.Connected) {S : Finset V}
    (h : CD G S) : radius G ≤ radius (G.induce (S : Set V)) + 1 := by
  let J := G.induce (S : Set V)
  obtain ⟨v, hv⟩ := center_exists J h.1
  apply radius_to _ v.val
  have cast_dist (w : (S : Set V)) : G.dist v.val w.val ≤ J.dist v w := by
    let F : J →g G := ⟨Subtype.val,fun e => e⟩
    obtain ⟨p,hp⟩ := h.1.exists_walk_length_eq_dist v w
    calc G.dist v.val w.val ≤ (p.map F).length := G.dist_le _
      _ = J.dist v w := (Walk.length_map F p).trans hp
  intro x
  change G.dist v.val x ≤ radius J + 1
  rcases h.2 x with hit|⟨y,hy,e⟩
  · have near := (cast_dist ⟨x,hit⟩).trans (hv ⟨x,hit⟩)
    change G.dist v.val x ≤ radius J at near
    omega
  · have near := (cast_dist ⟨y,hy⟩).trans (hv ⟨y,hy⟩)
    change G.dist v.val y ≤ radius J at near
    have t : G.dist v.val x ≤ G.dist v.val y + G.dist y x := hc.dist_triangle
    rw [dist_eq_one_iff_adj.mpr e.symm] at t
    omega

private theorem four_induce {S : Set V} (h4 : FourCycleFree G) :
    FourCycleFree (G.induce S) := by
  intro a b c d ne ac bc ad bd
  exact Subtype.ext (h4 a.val b.val c.val d.val (fun e => ne (Subtype.ext e)) ac bc ad bd)

private theorem no_induce {S : Set V} {n : ℕ} (h : NoPath G n) : NoPath (G.induce S) n := by
  rintro ⟨p,hp⟩
  exact h ⟨Subtype.val ∘ p, Subtype.val_injective.comp hp.1, hp.2⟩

private theorem no_inside_to_no_induce {S : Finset V} {n : ℕ} (h : NoPathIn G S n) :
    NoPath (G.induce (S : Set V)) n := by
  rintro ⟨p,hp⟩
  exact h ⟨Subtype.val ∘ p, ⟨Subtype.val_injective.comp hp.1, hp.2⟩,fun i => (p i).property⟩

private theorem radius_of_no_four_path (hc : G.Connected) (h4 : FourCycleFree G)
    (h : NoPath G 4) : radius G ≤ 1 := by
  classical
  by_cases n : ∃ x y, x ≠ y ∧ ¬ G.Adj x y
  · by_contra! hi
    obtain ⟨k,hk,p,hp,hp'⟩ := path_at_least_radius_add_two G hc h4 n
    exact h (trim_path (by omega) ⟨hp,hp'⟩)
  · push_neg at n
    obtain ⟨v⟩ := hc.nonempty
    apply radius_to _ v
    intro x
    by_cases e : v=x
    · subst x
      rw [dist_self]
      decide
    · exact le_of_eq (dist_eq_one_iff_adj.mpr (n _ _ e))

private theorem spanning_octagon_bound (H : Hole G 8) (sur : Function.Surjective H.c) :
    (∑ x, localIndependence G x) ≤ 2 * Fintype.card V := by
  classical
  have pt (v : V) : localIndependence G v ≤ 2 := by
    obtain ⟨i,rfl⟩ := sur v
    obtain ⟨A,hA,hc⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G := G) (H.c i)
    rw [←hc]
    have neigh := (Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).1
    let B := ({H.c (i+1), H.c (i-1)} : Finset V)
    have sub : A ⊆ B := by
      intro y hy
      obtain ⟨j,rfl⟩ := sur y
      have ed := (H.adj i j).mp (neigh _ hy)
      have ij : ∀ i j : Fin 8, Cyclic i j → j=i+1 ∨ j=i-1 := by decide
      rcases ij i j ed with ee|ee
      · simp [B,ee]
      · simp [B,ee]
    exact (Finset.card_le_card sub).trans Finset.card_le_two
  calc (∑ x, localIndependence G x) ≤ ∑ _x : V, 2 := Finset.sum_le_sum (fun x _ => pt x)
    _ = 2 * Fintype.card V := by simp [Nat.mul_comm]

theorem induced_eight_or_radius_three (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G) (dense : 3 * Fintype.card V ≤ ∑ x, localIndependence G x) :
    (∃ p : Fin 8 → V, InducedPath G p) ∨ radius G ≤ 3 := by
  classical
  by_cases no : NoPath G 8
  · right
    have hx6 (H : Hole G 6) (dom : ∀ x, Outside H.c x → ∃ i, G.Adj x (H.c i)) : radius G ≤ 3 := by
      rcases Graffiti133DominatingHex.dominating_hex_radius_or_strict_density H hc h4 no dom with h|h
      · exact h
      · omega
    rcases connected_domination_decomposition G hc 6 (by decide) no with ⟨D,hD,noD⟩|⟨H,dom⟩
    · let J := G.induce (D : Set V)
      have noJ : NoPath J 6 := no_inside_to_no_induce noD
      have fourJ : FourCycleFree J := four_induce h4
      rcases connected_domination_decomposition J hD.1 4 (by decide) noJ with ⟨E,hE,noE⟩|⟨H,dom⟩
      · have noK := no_inside_to_no_induce noE
        have small := radius_of_no_four_path hE.1 (four_induce fourJ) noK
        have a := radius_of_cd hD.1 hE
        have b := radius_of_cd hc hD
        change radius J ≤ radius (J.induce (E : Set (D : Set V)))+1 at a
        change radius G ≤ radius J+1 at b
        omega
      · let F : Graffiti133DominatingHex.Frame J :=
          { toHole := H, h4 := fourJ, no8 := no_induce no, dom := dom }
        rcases F.P6free_hex_radius_two_or_spans hD.1 noJ with new|spans
        · have b := radius_of_cd hc hD
          change radius J ≤ 2 at new
          change radius G ≤ radius J+1 at b
          omega
        · let K : Hole G 6 := ⟨Subtype.val ∘ H.c, Subtype.val_injective.comp H.inj,H.adj⟩
          apply hx6 K
          intro x hx
          rcases hD.2 x with on|⟨y,hy,e⟩
          · obtain ⟨i,eq⟩ := spans (⟨x,on⟩ : (D : Set V))
            exact (hx i (congrArg Subtype.val eq).symm).elim
          · obtain ⟨i,eq⟩ := spans (⟨y,hy⟩ : (D : Set V))
            refine ⟨i,?_⟩
            change G.Adj x ((F.c i).val)
            rw [eq]
            exact e
    · rcases Graffiti133Eighth.radius_le_three_or_spans_of_dominating_octagon_allow_five H hc h4 no dom with hh|sur
      · exact hh
      · letI := hc.nonempty
        have pos : 0 < Fintype.card V := Fintype.card_pos
        have bd := spanning_octagon_bound H sur
        omega
  · exact Or.inl (Classical.not_not.mp no)

#print axioms induced_eight_or_radius_three
end Graffiti133FinalEight
