import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Cazenave
open Finset SimpleGraph
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def randic : ℝ :=
  (∑ a : G.Dart, (√((G.degree a.fst : ℝ) * G.degree a.snd))⁻¹) / 2

/-- The usual Randić edge weight, symmetric in the two endpoints. -/
noncomputable def edgeWeight : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => (√((G.degree u : ℝ) * G.degree v))⁻¹,
    fun _ _ => by dsimp; rw [mul_comm]⟩

/-- The dart normalization equals the conventional sum over unordered edges. -/
theorem randic_eq_sum_edges :
    randic G = ∑ e ∈ G.edgeFinset, edgeWeight G e := by
  classical
  have hm (d : G.Dart) (_ : d ∈ (univ : Finset G.Dart)) :
      d.edge ∈ G.edgeFinset := mem_edgeFinset.mpr d.edge_mem
  have h := Finset.sum_fiberwise_of_maps_to' hm (edgeWeight G)
  have fiber (e : Sym2 V) (he : e ∈ G.edgeFinset) :
      (∑ _d ∈ (univ : Finset G.Dart).filter (fun d => d.edge = e), edgeWeight G e) =
        2 * edgeWeight G e := by
    rw [sum_const, G.dart_edge_fiber_card e (mem_edgeFinset.mp he)]
    norm_num
  have hh : (∑ d : G.Dart, edgeWeight G d.edge) =
      2 * ∑ e ∈ G.edgeFinset, edgeWeight G e := by
    rw [← h, Finset.mul_sum]
    exact sum_congr rfl fiber
  change (∑ d : G.Dart, edgeWeight G d.edge) / 2 = _
  rw [hh]
  ring

omit [DecidableEq V] in
private theorem positive_degree {a b : V} (h : G.Adj a b) : (0:ℝ) < G.degree a := by
  exact_mod_cast Finset.card_pos.mpr ⟨b, (G.mem_neighborFinset a b).mpr h⟩

private theorem sum_offdiag (f : V → ℝ) :
    (∑ a ∈ (univ : Finset (V × V)).filter (fun a => a.1 ≠ a.2), f a.1 * f a.2) =
      (∑ v, f v) ^ 2 - ∑ v, f v ^ 2 := by
  classical
  rw [sum_filter, Fintype.sum_prod_type]
  have h (x y : V) : (if x ≠ y then f x * f y else 0) =
    f x * f y - if x = y then f x ^ 2 else 0 := by
    by_cases e : x = y
    · subst y; simp [pow_two]
    · simp [e]
  simp_rw [h, sum_sub_distrib, ← mul_sum]
  rw [← sum_mul]
  simp [pow_two]

/-- Conjecture 6(i) in arXiv:2611.03879v1. -/
theorem randic_sq_lower (hc : G.Connected) (hn : 2 ≤ Fintype.card V) :
    ((G.edgeFinset.card : ℝ) + 1) / 2 ≤ (randic G) ^ 2 := by
  classical
  let f (v : V) : ℝ := G.degree v
  let m : ℝ := G.edgeFinset.card
  let w (a : G.Dart) := f a.fst * f a.snd
  let S := ∑ a : G.Dart, (√(w a))⁻¹
  let U := ∑ a : G.Dart, √(w a)
  let T := ∑ a : G.Dart, w a
  let Q := ∑ v, f v ^ 2
  have hvn : Fintype.card V ≤ G.edgeFinset.card + 1 := by
    simpa using hc.card_vert_le_card_edgeSet_add_one
  have hnv : (Fintype.card V : ℝ) ≤ m+1 := by
    dsimp [m]
    exact_mod_cast hvn
  have hm : 0 < m := by
    change 0 < (G.edgeFinset.card : ℝ)
    exact_mod_cast (show 0 < G.edgeFinset.card by omega)
  have deg : ∑ v, f v = 2*m := by
    dsimp [f,m]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have nc : (Fintype.card G.Dart : ℝ) = 2*m := by
    dsimp [m]
    exact_mod_cast G.dart_card_eq_twice_card_edges
  have hp (a : G.Dart) : 0 < w a :=
    mul_pos (positive_degree G a.adj) (positive_degree G a.adj.symm)
  have hU : 0 < U := by
    apply sum_pos
    · exact fun a _ => Real.sqrt_pos.2 (hp a)
    · rw [← Finset.card_pos, Finset.card_univ]
      have raw := G.dart_card_eq_twice_card_edges
      have em : 0 < G.edgeFinset.card := by omega
      omega
  have hS : 0 ≤ S := sum_nonneg fun a _ => inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hQ : 0 ≤ Q := sum_nonneg fun _ _ => sq_nonneg _
  have hq : (2*m)^2 ≤ (m+1)*Q := by
    have t := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset V) f (fun _ => (1:ℝ))
    simp only [mul_one, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one] at t
    rw [deg] at t
    exact t.trans (by simpa [Q, mul_comm] using mul_le_mul_of_nonneg_right hnv hQ)
  have ht : T ≤ (2*m)^2-Q := by
    let b (a : G.Dart) : V × V := (a.fst,a.snd)
    have inj : Function.Injective b := by
      intro a c h
      cases a; cases c
      aesop
    rw [← deg, ← sum_offdiag]
    change (∑ a ∈ (univ : Finset G.Dart), f (b a).1 * f (b a).2) ≤ _
    rw [← Finset.sum_image (s := (univ : Finset G.Dart)) (g := b)
      (f := fun p : V × V => f p.1 * f p.2) (fun a _ c _ e => inj e)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro z hz
      obtain ⟨a,_,rfl⟩ := mem_image.mp hz
      exact mem_filter.mpr ⟨mem_univ _,G.ne_of_adj a.adj⟩
    · intro p _ _
      exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have htu : (m+1)*T ≤ 4*m^3 := by
    have h := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ m+1)
    linarith only [h, hq]
  have hc₁ : (2*m)^2 ≤ S*U := by
    have h := Finset.sq_sum_div_le_sum_sq_div (univ : Finset G.Dart)
      (fun _ => (1:ℝ)) (g := fun a => √(w a)) (fun a _ => Real.sqrt_pos.2 (hp a))
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, one_pow, one_div] at h
    rw [nc] at h
    exact (div_le_iff₀ hU).mp h
  have hc₂ : U^2 ≤ (2*m)*T := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset G.Dart)
      (fun _ => (1:ℝ)) (fun a => √(w a))
    simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, nc,
      Real.sq_sqrt (hp _).le] at h
    exact h
  have hS2 : 0 ≤ S^2 := sq_nonneg _
  have p₁ := pow_le_pow_left₀ (sq_nonneg (2*m)) hc₁ 2
  have p₂ := mul_le_mul_of_nonneg_left hc₂ hS2
  have joint : (2*m)^4 ≤ S^2 * ((2*m)*T) := by
    calc
      _ = ((2*m)^2)^2 := by ring
      _ ≤ (S*U)^2 := p₁
      _ = S^2*U^2 := by ring
      _ ≤ _ := p₂
  have joint' : (2*m)^3 ≤ S^2*T := by
    apply (mul_le_mul_left (by positivity : 0 < 2*m)).mp
    calc
      (2*m)*(2*m)^3 = (2*m)^4 := by ring
      _ ≤ S^2*((2*m)*T) := joint
      _ = (2*m)*(S^2*T) := by ring
  have big : ((m+1)*2) * (4*m^3) ≤ S^2 * (4*m^3) := by
    calc
      _ = (m+1)*(2*m)^3 := by ring
      _ ≤ (m+1)*(S^2*T) := mul_le_mul_of_nonneg_left joint' (by positivity)
      _ = S^2*((m+1)*T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htu hS2
  have final := (mul_le_mul_right (by positivity : 0 < 4*m^3)).mp big
  change (m+1)/2 ≤ (S/2)^2
  nlinarith [final]

theorem randic_sq_lower_edges (hc : G.Connected) (hn : 2 ≤ Fintype.card V) :
    ((G.edgeFinset.card : ℝ) + 1) / 2 ≤ (∑ e ∈ G.edgeFinset, edgeWeight G e) ^ 2 := by
  rw [← randic_eq_sum_edges]
  exact randic_sq_lower G hc hn

#print axioms Cazenave.randic_sq_lower_edges
end Cazenave
