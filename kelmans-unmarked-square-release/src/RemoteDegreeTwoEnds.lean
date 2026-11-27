import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace KelmansCactus.AtomicBridge.RemoteDegreeTwoEnds
open SimpleGraph Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Connected finite 1/2-degree graph with at least one endpoint has exactly
two endpoints. This is the graph-theoretic ingredient for extracting outside
matching strips automatically. -/
theorem count_endpoints (connected : G.Connected)
    (degree : ∀ x,G.degree x=1 ∨ G.degree x=2) {a : V} (endpoint : G.degree a=1) :
    (Finset.univ.filter fun x=>G.degree x=1).card=2 := by
  classical
  let B : Finset V := Finset.univ.filter fun x=>G.degree x=1
  have oddSet : (Finset.univ.filter fun x=>Odd (G.degree x))=B := by
    ext x
    rcases degree x with h|h <;> simp [B,h]
  have h_even := G.even_card_odd_degree_vertices
  rw [oddSet] at h_even
  have non : 0<B.card := (Finset.card_pos).mpr ⟨a,by simp [B,endpoint]⟩
  have edge := connected.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,←G.edgeFinset_card] at edge
  have dsum := G.sum_degrees_eq_twice_card_edges
  have equal : (∑ x : V,G.degree x)+B.card=2*Fintype.card V := by
    classical
    rw [Finset.card_eq_sum_ones, show (∑ x∈B,(1:Nat)) =
        ∑ x : V, if G.degree x=1 then 1 else 0 by
          rw [←Finset.sum_filter]]
    rw [←Finset.sum_add_distrib]
    have all (x : V) : G.degree x+(if G.degree x=1 then 1 else 0)=2 := by
      rcases degree x with h|h <;> simp [h]
    simp [all,Nat.mul_comm]
  obtain ⟨k,hk⟩ := h_even
  change B.card=2
  omega

#print axioms count_endpoints
end KelmansCactus.AtomicBridge.RemoteDegreeTwoEnds
