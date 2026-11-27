import RankBound

namespace CazenaveRank
open Finset SimpleGraph
open scoped BigOperators
set_option autoImplicit false
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The standard Randić weight of an unordered edge. -/
noncomputable def conventionalWeight : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => 1/(Real.sqrt ((G.degree u : ℝ) * G.degree v)),
    fun _ _ => by dsimp; rw [mul_comm]⟩

/-- The row-sum convention of the proof equals the conventional unordered-edge index. -/
theorem randic_eq_unordered : randic G = ∑ e ∈ G.edgeFinset, conventionalWeight G e := by
  classical
  have hmap (d : G.Dart) (_ : d ∈ (Finset.univ : Finset G.Dart)) : d.fst ∈ Finset.univ :=
    Finset.mem_univ _
  have hf := Finset.sum_fiberwise_of_maps_to hmap (fun d => conventionalWeight G d.edge)
  have hh : (∑ u : V, ∑ v ∈ G.neighborFinset u, 1/(Real.sqrt (G.degree u) * Real.sqrt (G.degree v))) =
      ∑ d : G.Dart, conventionalWeight G d.edge := by
    rw [← hf]
    apply Finset.sum_congr rfl
    intro u _
    rw [G.dart_fst_fiber]
    rw [Finset.sum_image (fun a _ b _ h => G.dartOfNeighborSet_injective u h)]
    rw [Finset.sum_subtype (G.neighborFinset u)
      (fun v => (G.mem_neighborFinset u v).trans Iff.rfl)]
    apply Finset.sum_congr rfl
    intro v _
    change 1/(Real.sqrt (G.degree u)*Real.sqrt (G.degree (v : V))) =
      1/(Real.sqrt ((G.degree u : ℝ)*G.degree (v : V)))
    rw [Real.sqrt_mul (Nat.cast_nonneg _)]
  have hm (d : G.Dart) (_ : d ∈ (univ : Finset G.Dart)) :
      d.edge ∈ G.edgeFinset := mem_edgeFinset.mpr d.edge_mem
  have h := Finset.sum_fiberwise_of_maps_to' hm (conventionalWeight G)
  have fiber (e : Sym2 V) (he : e ∈ G.edgeFinset) :
      (∑ _d ∈ (univ : Finset G.Dart).filter (fun d => d.edge = e), conventionalWeight G e) =
        2 * conventionalWeight G e := by
    rw [sum_const, G.dart_edge_fiber_card e (mem_edgeFinset.mp he)]
    norm_num
  have h₂ : (∑ d : G.Dart, conventionalWeight G d.edge) =
      2 * ∑ e ∈ G.edgeFinset, conventionalWeight G e := by
    rw [← h, Finset.mul_sum]
    exact sum_congr rfl fiber
  unfold randic
  rw [hh,h₂]
  ring

#print axioms randic_eq_unordered
end CazenaveRank
