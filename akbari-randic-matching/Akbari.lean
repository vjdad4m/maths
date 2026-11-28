import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace AkbariRandic
open SimpleGraph Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def weight : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => (Real.sqrt ((G.degree u : ℝ) * G.degree v))⁻¹,
    fun _ _ => by dsimp; rw [mul_comm]⟩

noncomputable def randic : ℝ := ∑ e ∈ G.edgeFinset, weight G e

/-- A matching indexed by its edges, with the two endpoints of each edge. -/
def HasMatching (k : ℕ) : Prop :=
  ∃ f : Fin k × Bool ↪ V, ∀ i, G.Adj (f (i,false)) (f (i,true))

noncomputable def matchingNumber : ℕ := sSup {k | HasMatching G k}

omit [DecidableEq V] in
private theorem weight_nonneg (e : Sym2 V) : 0 ≤ weight G e := by
  induction e using Sym2.ind with
  | h a b => exact inv_nonneg.mpr (Real.sqrt_nonneg _)

omit [DecidableEq V] in
private theorem randic_nonneg : 0 ≤ randic G := sum_nonneg (fun e _ => weight_nonneg G e)

omit [DecidableEq V] in
private theorem real_degree_sum :
    (∑ v : V, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

private def dartProd (d : G.Dart) : ℝ := (G.degree d.fst : ℝ) * G.degree d.snd

omit [DecidableEq V] in
private theorem dartProd_pos (d : G.Dart) : 0 < dartProd G d := by
  unfold dartProd
  exact mul_pos (by exact_mod_cast (G.degree_pos_iff_exists_adj _).mpr ⟨_,d.adj⟩)
    (by exact_mod_cast (G.degree_pos_iff_exists_adj _).mpr ⟨_,d.adj.symm⟩)

omit [DecidableEq V] in
private theorem sum_dart_prod :
    (∑ d : G.Dart, dartProd G d) ≤ (2 * (G.edgeFinset.card : ℝ))^2 := by
  let f : V × V → ℝ := fun p => (G.degree p.1 : ℝ) * G.degree p.2
  let emb : G.Dart ↪ V × V := ⟨fun d => d.toProd, by
    intro a b h
    cases a
    cases b
    congr⟩
  calc
    _ = ∑ p ∈ (univ : Finset G.Dart).map emb, f p := (sum_map _ _ _).symm
    _ ≤ ∑ p : V × V, f p := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun p _ _ => by
      dsimp [f]; positivity)
    _ = (2 * (G.edgeFinset.card : ℝ))^2 := by
      rw [← univ_product_univ, sum_product]
      simp only [f, ← mul_sum, ← sum_mul, real_degree_sum]
      ring

private theorem sum_dart_recip :
    (∑ d : G.Dart, (Real.sqrt (dartProd G d))⁻¹) = 2 * randic G := by
  have hm (d : G.Dart) (_ : d ∈ (univ : Finset G.Dart)) :
      d.edge ∈ G.edgeFinset := mem_edgeFinset.mpr d.edge_mem
  have h := Finset.sum_fiberwise_of_maps_to' hm (weight G)
  change (∑ d : G.Dart, weight G d.edge) = _
  rw [← h,randic,Finset.mul_sum]
  apply sum_congr rfl
  intro e he
  rw [sum_const, G.dart_edge_fiber_card e (mem_edgeFinset.mp he)]
  norm_num

theorem edge_count_le_two_randic_sq :
    (G.edgeFinset.card : ℝ) ≤ 2 * randic G ^ 2 := by
  let N : ℝ := 2 * (G.edgeFinset.card : ℝ)
  let s := ∑ d : G.Dart, Real.sqrt (dartProd G d)
  have n_card : (Fintype.card G.Dart : ℝ) = N := by
    dsimp [N]; exact_mod_cast G.dart_card_eq_twice_card_edges
  have hs : 0 ≤ s := sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hR := randic_nonneg G
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have A : N^2 ≤ s * (2 * randic G) := by
    have c := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (univ : Finset G.Dart)
      (r := fun _ => (1:ℝ)) (f := fun d => Real.sqrt (dartProd G d))
      (g := fun d => (Real.sqrt (dartProd G d))⁻¹)
      (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
      (fun d _ => by rw [mul_inv_cancel₀ (Real.sqrt_pos_of_pos (dartProd_pos G d)).ne']; norm_num)
    simpa [s, sum_dart_recip, n_card] using c
  have B : s^2 ≤ N^3 := by
    have c := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (univ : Finset G.Dart)
      (r := fun d => Real.sqrt (dartProd G d)) (f := fun _ => (1:ℝ)) (g := dartProd G)
      (fun _ _ => zero_le_one) (fun d _ => (dartProd_pos G d).le)
      (fun d _ => by rw [Real.sq_sqrt (dartProd_pos G d).le, one_mul])
    have c' : s^2 ≤ N * (∑ d : G.Dart, dartProd G d) := by simpa [s,n_card] using c
    calc
      _ ≤ N * N^2 := c'.trans (mul_le_mul_of_nonneg_left (sum_dart_prod G) hN)
      _ = _ := by ring
  by_cases bz : N = 0
  · dsimp [N] at bz; nlinarith [sq_nonneg (randic G)]
  have hn : 0 < N := lt_of_le_of_ne hN (Ne.symm bz)
  have C : N^2 * N^2 ≤ (s * (2*randic G)) * (s * (2*randic G)) :=
    mul_le_mul A A (sq_nonneg _) (by positivity)
  have D := mul_le_mul_of_nonneg_right B (sq_nonneg (2*randic G))
  have E : N^3 * N ≤ N^3 * (2*randic G)^2 := by
    calc
      _ = N^2 * N^2 := by ring
      _ ≤ (s * (2*randic G)) * (s * (2*randic G)) := C
      _ = s^2 * (2*randic G)^2 := by ring
      _ ≤ _ := D
  have e := le_of_mul_le_mul_left E (pow_pos hn 3)
  dsimp [N] at e
  nlinarith

set_option maxHeartbeats 400000 in
omit [DecidableEq V] in
theorem matching_sq_le_edges_times_randic {k : ℕ} (h : HasMatching G k) :
    (k : ℝ)^2 ≤ (G.edgeFinset.card : ℝ) * randic G := by
  obtain ⟨f,ha⟩ := h
  let p (i : Fin k) : ℝ := (G.degree (f (i,false)) : ℝ) * G.degree (f (i,true))
  let s (i : Fin k) : ℝ := Real.sqrt (p i)
  have hp (i : Fin k) : 0 < p i := dartProd_pos G (⟨(f (i,false), f (i,true)),ha i⟩ : G.Dart)
  have hi : Function.Injective (fun i : Fin k => s(f (i,false), f (i,true))) := by
    intro i j e
    rcases Sym2.eq_iff.mp e with ⟨e1,_⟩ | ⟨e1,_⟩
    · exact congrArg Prod.fst (f.injective e1)
    · have bad := congrArg Prod.snd (f.injective e1)
      cases bad
  let em : Fin k ↪ Sym2 V := ⟨_,hi⟩
  have hweight : (∑ i : Fin k, (s i)⁻¹) ≤ randic G := by
    have sub : (univ : Finset (Fin k)).map em ⊆ G.edgeFinset := by
      intro e he
      obtain ⟨i,_,rfl⟩ := mem_map.mp he
      exact mem_edgeFinset.mpr ((G.mem_edgeSet).mpr (ha i))
    calc
      _ = ∑ e ∈ (univ : Finset (Fin k)).map em, weight G e := by
        rw [sum_map]
        apply sum_congr rfl
        intro i _
        rfl
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (fun e _ _ => weight_nonneg G e)
  have hend : (∑ i : Fin k, ((G.degree (f (i,false)) : ℝ) + G.degree (f (i,true)))) ≤
      2 * (G.edgeFinset.card : ℝ) := by
    rw [← real_degree_sum]
    calc
      _ = ∑ x : Fin k × Bool, (G.degree (f x) : ℝ) := by
        rw [← univ_product_univ, sum_product]
        simp [Fintype.univ_bool,add_comm]
      _ = ∑ v ∈ (univ : Finset (Fin k × Bool)).map f, (G.degree v : ℝ) :=
        (sum_map univ f (fun v => (G.degree v : ℝ))).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
  have hsum : (∑ i : Fin k, s i) ≤ (G.edgeFinset.card : ℝ) := by
    have hsm (i : Fin k) : 2 * s i ≤ ((G.degree (f (i,false)) : ℝ) + G.degree (f (i,true))) := by
      exact two_mul_le_add_of_sq_eq_mul (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        (Real.sq_sqrt (hp i).le)
    have e := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin k))) => hsm i)
    rw [← Finset.mul_sum] at e
    linarith
  have c := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (univ : Finset (Fin k))
    (r := fun _ => (1:ℝ)) (f := s) (g := fun i => (s i)⁻¹)
    (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
    (fun i _ => by rw [mul_inv_cancel₀ (Real.sqrt_pos_of_pos (hp i)).ne']; norm_num)
  have c' : (k : ℝ)^2 ≤ (∑ i : Fin k, s i) * ∑ i : Fin k, (s i)⁻¹ := by simpa using c
  have hs0 : 0 ≤ ∑ i : Fin k, (s i)⁻¹ := sum_nonneg (fun i _ =>
    inv_nonneg.mpr (Real.sqrt_nonneg (p i)))
  exact c'.trans (mul_le_mul hsum hweight hs0 (Nat.cast_nonneg _))

theorem matching_cube_bound {k : ℕ} (h : HasMatching G k) :
    (k : ℝ)^2 ≤ 2 * (randic G)^3 := by
  calc
    _ ≤ (G.edgeFinset.card : ℝ) * randic G := matching_sq_le_edges_times_randic G h
    _ ≤ (2 * randic G ^ 2) * randic G :=
      mul_le_mul_of_nonneg_right (edge_count_le_two_randic_sq G) (randic_nonneg G)
    _ = _ := by ring

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem matchingNumber_attained : HasMatching G (matchingNumber G) := by
  have empty : HasMatching G 0 := ⟨⟨fun p => Fin.elim0 p.1, fun p => Fin.elim0 p.1⟩, fun i => Fin.elim0 i⟩
  have bounded : BddAbove {k | HasMatching G k} := by
    refine ⟨Fintype.card V,?_⟩
    rintro k ⟨f,_⟩
    have h := Fintype.card_le_of_injective f f.injective
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
    omega
  exact Nat.sSup_mem ⟨0,empty⟩ bounded

theorem matching_number_cube_bound :
    (matchingNumber G : ℝ)^2 ≤ 2 * randic G ^ 3 :=
  matching_cube_bound G (matchingNumber_attained G)

#print axioms edge_count_le_two_randic_sq
#print axioms matching_sq_le_edges_times_randic
#print axioms matching_number_cube_bound
end AkbariRandic
