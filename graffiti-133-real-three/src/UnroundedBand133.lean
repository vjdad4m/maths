import MoreBands133
import PentagonSparse133
import StrictDensity133

namespace Graffiti133Pentagon
namespace PentagonFrame
open SimpleGraph Graffiti133 Graffiti133Revisit Finset
open scoped BigOperators
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : PentagonFrame G)

private noncomputable def cycleDonation (x : V) : ℕ := by
  classical
  exact ∑ i : Fin 5, if x = F.c i then (F.singleSite i).card else 0

private noncomputable def outsideCost (x : V) : ℕ := by
  classical
  exact if Outside F.c x then 1 else 0

private theorem single_site_filter (i : Fin 5) :
    F.singleSite i = F.allSingles.filter (fun x => F.index x = i) := by
  classical
  ext x
  have hIdx (h : x ∈ F.allSingles) : One G F.c x (F.index x) := by
    have claim : ∃ j, One G F.c x j := (Finset.mem_filter.mp h).2
    unfold index
    rw [dif_pos claim]
    exact Classical.choose_spec claim
  have he : x ∈ F.singleSite i ↔ One G F.c x i := by simp [singleSite]
  rw [he,Finset.mem_filter]
  refine ⟨?_,fun ⟨h,he⟩ => he ▸ hIdx h⟩
  intro h
  have hx : x ∈ F.allSingles := Finset.mem_filter.mpr ⟨Finset.mem_univ _, i,h⟩
  exact ⟨hx,(h.2 _).mp (((hIdx hx).2 _).mpr rfl)⟩

private theorem donation_sum : (∑ x : V, F.cycleDonation x) = F.allSingles.card := by
  classical
  unfold cycleDonation
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simpa only [F.single_site_filter] using
    (Finset.card_eq_sum_card_fiberwise (s:=F.allSingles) (t:=Finset.univ)
      (f:=F.index) (fun _ _ => Finset.mem_univ _)).symm

private theorem pointwise_budget (rad : 2 < radius G) (x : V) :
    localIndependence G x + F.outsideCost x ≤ 2 + F.cycleDonation x := by
  classical
  by_cases out : Outside F.c x
  · have hl := F.sparse_outside rad out
    simp only [outsideCost,if_pos out]
    omega
  · obtain ⟨i,he⟩ : ∃ i, x = F.c i := by
      apply Classical.byContradiction
      intro h
      exact out (fun i e => h ⟨i,e⟩)
    have hd : (F.singleSite i).card ≤ F.cycleDonation x := by
      have hh := Finset.single_le_sum (f := fun j : Fin 5 =>
        if x = F.c j then (F.singleSite j).card else 0) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)
      simpa [cycleDonation,he] using hh
    have hb := F.local_cycle_bound i
    rw [← he] at hb
    simp only [outsideCost,if_neg out,Nat.add_zero]
    omega

include F in
theorem sparse_total_budget (rad : 2 < radius G) :
    (∑ x, localIndependence G x) ≤ 2 * Fintype.card V := by
  classical
  let E := (Finset.univ : Finset V).filter (Outside F.c)
  have sumcost : (∑ x, F.outsideCost x) = E.card := by
    simp [outsideCost,Finset.sum_ite,E]
  have subset : F.allSingles ⊆ E := by
    intro x hx
    obtain ⟨i,hi⟩ : ∃ i, One G F.c x i := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi.1⟩
  have cb := Finset.card_le_card subset
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun x _ => F.pointwise_budget rad x)
  have hu : (∑ x, localIndependence G x) + E.card ≤
      2 * Fintype.card V + F.allSingles.card := by
    simpa [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      sumcost,F.donation_sum,Nat.mul_comm] using hs
  omega

include F in
theorem sparse_mean (rad : 2 < radius G) : averageLocal G ≤ 2 := by
  classical
  letI : Nonempty V := ⟨F.c 0⟩
  have bd := F.sparse_total_budget rad
  unfold averageLocal
  have hN : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α:=V)
  apply (div_le_iff₀ hN).mpr
  rw [← Nat.cast_sum]
  exact_mod_cast bd

#print axioms sparse_mean

end PentagonFrame
end Graffiti133Pentagon

namespace Graffiti133Revisit
open SimpleGraph Graffiti133 Graffiti133Pentagon
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V]

/-- In any connected four-cycle-free graph, if local mean is above two
and radius is above two, then an induced six-vertex path exists. -/
theorem P6_or_radius_two_of_mean_gt_two (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G) (ha : 2 < averageLocal G) :
    (∃ f : Fin 6 → V, InducedPath G f) ∨ radius G ≤ 2 := by
  classical
  letI := hc.nonempty
  by_cases h5 : NoSimpleFive133 G
  · exact Or.inl (P6_of_local_mean_gt_two_without_five G h4 h5 ha)
  · by_cases hp : ∃ p : Fin 6 → V, InducedPath G p
    · exact Or.inl hp
    · obtain ⟨F⟩ := make_frame hc h4 h5 hp
      apply Or.inr
      exact Nat.le_of_not_gt (fun ht => (not_le_of_gt ha) (F.sparse_mean ht))

/-- The unrounded version of #133 for all connected graphs with local mean
at most three: no restriction on radius, degrees or cycles. -/
theorem conjecture133_real_full_three (G : SimpleGraph V) (hc : G.Connected)
    (ha : averageLocal G ≤ 3) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · by_cases hSmall : averageLocal G ≤ 2
    · exact conjecture133_low_average_or_four_cycle G hc (Or.inr hSmall)
    · by_cases hr : radius G ≤ 3
      · rcases P6_or_radius_two_of_mean_gt_two G hc h4 (lt_of_not_ge hSmall) with ⟨p,hp⟩ | hr2
        · refine ⟨6,?_,p,hp⟩
          simp only [rhs133,if_pos h4,pow_one]
          change (radius G : ℚ) + averageLocal G ≤ 6
          have hR : (radius G : ℚ) ≤ 3 := by exact_mod_cast hr
          linarith
        · exact conjecture133_real_three_radius_two G hc hr2 ha
      · apply conjecture133_unrounded_high_radius G hc
        have hR : (4 : ℚ) ≤ radius G := by exact_mod_cast (show 4 ≤ radius G by omega)
        linarith
  · exact conjecture133_low_average_or_four_cycle G hc (Or.inl h4)

#print axioms P6_or_radius_two_of_mean_gt_two
#print axioms conjecture133_real_full_three

end Graffiti133Revisit
