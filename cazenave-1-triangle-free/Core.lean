import Mathlib.Data.Real.Sqrt
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.Positivity

namespace CazenaveOne
open Finset SimpleGraph
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

def TriangleFree {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ u v w : V, G.Adj u v → G.Adj u w → ¬ G.Adj v w

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The degrees in any independent set count distinct edges. -/
theorem sum_independent_degrees (s : Finset V)
    (hs : ∀ v ∈ s, ∀ w ∈ s, ¬ G.Adj v w) :
    (∑ v ∈ s, G.degree v) ≤ G.edgeFinset.card := by
  classical
  let D := (Finset.univ : Finset G.Dart).filter (fun d => d.fst ∈ s)
  have hMaps : Set.MapsTo (fun d : G.Dart => d.fst) D s :=
    fun d hd => (Finset.mem_filter.mp hd).2
  have hfiber := Finset.card_eq_sum_card_fiberwise hMaps
  have sumeq : D.card = ∑ v ∈ s, G.degree v := by
    rw [hfiber]
    apply Finset.sum_congr rfl
    intro v hv
    rw [← G.dart_fst_fiber_card_eq_degree v]
    congr 1
    ext d
    simp [D,show d.fst ∈ s ∧ d.fst = v ↔ d.fst = v by
      constructor
      · exact And.right
      · intro e; exact ⟨e ▸ hv,e⟩]
  have hj : Set.InjOn (fun d : G.Dart => d.edge) D := by
    intro a ha b hb eq
    rcases (G.dart_edge_eq_iff a b).mp eq with rfl | eq
    · rfl
    · exfalso
      have hah : a.fst ∈ s := (Finset.mem_filter.mp ha).2
      have hbh : b.fst ∈ s := (Finset.mem_filter.mp hb).2
      have hsh : b.snd ∈ s := by simpa [eq] using hah
      exact hs b.fst hbh b.snd hsh b.adj
  have hsub : D.image (fun d : G.Dart => d.edge) ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp he
    exact mem_edgeFinset.mpr a.edge_mem
  rw [← sumeq,← Finset.card_image_of_injOn hj]
  exact Finset.card_le_card hsub

theorem triangleFree_neighbor_mass (h : TriangleFree G) (u : V) :
    (∑ v ∈ G.neighborFinset u, G.degree v) ≤ G.edgeFinset.card := by
  apply sum_independent_degrees
  exact fun v hv w hw => h u v w ((G.mem_neighborFinset u v).mp hv)
    ((G.mem_neighborFinset u w).mp hw)

/-- Two-neighbourhood counting proves the weighted degree-product bound. -/
theorem triangleFree_dart_degree_product (h : TriangleFree G) :
    (∑ a : G.Dart, (G.degree a.fst : ℝ) * G.degree a.snd) ≤
      2 * (G.edgeFinset.card : ℝ)^2 := by
  classical
  have hmap (d : G.Dart) (_ : d ∈ (Finset.univ : Finset G.Dart)) : d.fst ∈ Finset.univ :=
    Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hf (v : V) : (∑ a ∈ ({d : G.Dart | d.fst = v} : Finset _),
      (G.degree a.fst : ℝ) * G.degree a.snd) =
      (G.degree v : ℝ) * (∑ w ∈ G.neighborFinset v, (G.degree w : ℝ)) := by
    rw [G.dart_fst_fiber, Finset.sum_image (fun a _ b _ hh => G.dartOfNeighborSet_injective v hh),
      Finset.mul_sum]
    rw [Finset.sum_subtype (G.neighborFinset v) (fun w => (G.mem_neighborFinset v w).trans Iff.rfl)]
    rfl
  simp_rw [hf]
  have hb (v : V) : (G.degree v : ℝ) * (∑ w ∈ G.neighborFinset v, (G.degree w : ℝ)) ≤
      (G.degree v : ℝ) * G.edgeFinset.card := by
    have hs := triangleFree_neighbor_mass G h v
    have hcast : ((∑ w ∈ G.neighborFinset v, G.degree w : ℕ) : ℝ) ≤
        G.edgeFinset.card := by exact_mod_cast hs
    push_cast at hcast
    exact mul_le_mul_of_nonneg_left hcast (Nat.cast_nonneg _)
  refine (Finset.sum_le_sum (fun v _ => hb v)).trans_eq ?_
  rw [← Finset.sum_mul]
  have hs : (∑ v : V, (G.degree v : ℝ)) = 2 * G.edgeFinset.card := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [hs]
  ring

/-- The standard Randić weight of an unordered edge. -/
noncomputable def conventionalWeight : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => 1/(Real.sqrt ((G.degree u : ℝ) * G.degree v)),
    fun _ _ => by dsimp; rw [mul_comm]⟩

/-- The conventional Randić index, summed over unordered edges. -/
noncomputable def randic : ℝ := ∑ e ∈ G.edgeFinset, conventionalWeight G e

/-- Purely combinatorial proof of the triangle-free bound R≥sqrt(m). -/
theorem triangleFree_randic (h : TriangleFree G) :
    Real.sqrt (G.edgeFinset.card : ℝ) ≤ randic G := by
  classical
  let m : ℝ := G.edgeFinset.card
  let W (a : G.Dart) := Real.sqrt ((G.degree a.fst : ℝ) * G.degree a.snd)
  let U : ℝ := ∑ a, W a
  let S : ℝ := ∑ a, 1/W a
  have hp (a : G.Dart) : 0 < W a := by
    apply Real.sqrt_pos.2
    apply mul_pos <;> exact_mod_cast (G.degree_pos_iff_exists_adj _).2 ⟨_, by first | exact a.adj | exact a.adj.symm⟩
  have hS : 0 ≤ S := Finset.sum_nonneg fun a _ => one_div_nonneg.mpr (hp a).le
  by_cases H : 0 < G.edgeFinset.card
  · have hm : 0 < m := by dsimp [m]; exact_mod_cast H
    have hU : 0 < U := by
      apply Finset.sum_pos (fun a _ => hp a)
      rw [← Finset.card_pos,Finset.card_univ,G.dart_card_eq_twice_card_edges]
      omega
    have hNd : (Fintype.card G.Dart : ℝ)=2*m := by dsimp [m]; exact_mod_cast G.dart_card_eq_twice_card_edges
    have h1 : (2*m)^2 ≤ S*U := by
      have hh := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset G.Dart) (fun _ => (1:ℝ))
        (g := W) (fun a _ => hp a)
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, one_pow,hNd] at hh
      have hs := (div_le_iff₀ hU).mp hh
      exact hs
    have hT : (∑ a : G.Dart, W a ^ 2) ≤ 2*m^2 := by
      simp_rw [W,Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
      exact triangleFree_dart_degree_product G h
    have h2 : U^2 ≤ (2*m)*(2*m^2) := by
      have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset G.Dart) W (fun _ => (1:ℝ))
      simp only [mul_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,one_pow,hNd] at hh
      rw [mul_comm] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left hT (by positivity))
    let root := Real.sqrt m
    have hr : 0 < root := Real.sqrt_pos.2 hm
    have hrs : root^2=m := Real.sq_sqrt hm.le
    have ub : U ≤ 2*m*root := by
      have hs : U^2≤(2*m*root)^2 := by
        calc
          _ ≤ (2*m)*(2*m^2) := h2
          _ = _ := by ring_nf; rw [hrs]; ring
      exact (sq_le_sq₀ hU.le (by positivity)).mp hs
    have hh := mul_le_mul_of_nonneg_left ub hS
    have lower : 2*root ≤ S := by
      have hthird : (2*m)^2 ≤ S*(2*m*root) := h1.trans hh
      apply le_of_mul_le_mul_right ?_ (show 0<2*m*root by positivity)
      have he : 2*root*(2*m*root) = (2*m)^2 := by
        calc
          _ = 4*m*root^2 := by ring
          _ = _ := by rw [hrs]; ring
      rw [he]
      exact hthird
    change root ≤ _
    unfold randic
    have he : S = 2 * ∑ e ∈ G.edgeFinset, conventionalWeight G e := by
      have hh := Finset.sum_fiberwise_of_maps_to' (fun d : G.Dart => fun _ : d ∈ Finset.univ =>
        mem_edgeFinset.mpr d.edge_mem) (conventionalWeight G)
      rw [← show (∑ a : G.Dart, 1/W a) = ∑ a : G.Dart, conventionalWeight G a.edge from rfl]
        at hh
      change (∑ a : G.Dart, 1/W a) = 2 * ∑ e ∈ G.edgeFinset, conventionalWeight G e
      rw [← hh,Finset.mul_sum]
      apply Finset.sum_congr rfl
      exact fun e he => by rw [Finset.sum_const,G.dart_edge_fiber_card e (mem_edgeFinset.mp he)]; norm_num
    linarith only [he,lower]
  · have h0 : G.edgeFinset.card = 0 := by omega
    rw [h0,Nat.cast_zero,Real.sqrt_zero]
    rw [randic,Finset.card_eq_zero.mp h0,Finset.sum_empty]

#print axioms sum_independent_degrees
#print axioms triangleFree_randic
end CazenaveOne
