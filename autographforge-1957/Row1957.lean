import Twin
import Archive
import DegreeBound
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Archimedean.Basic

namespace RegularCliques1957
open SimpleGraph HallRainbow1121 TriangleMatching1078 AutoGraphForge378

theorem catalogue_factor_two {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (orderG : 2 ≤ Fintype.card V) (conn : G.Connected)
    {d : ℕ} (reg : G.IsRegularOfDegree d) :
    vertexCliqueCover G ≤ 2 * lineDomination G := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp orderG
  let v := Classical.arbitrary V
  obtain ⟨w,diff⟩ := exists_ne v
  obtain ⟨walk⟩ := conn.preconnected v w
  have pos : 0 < G.degree v := by
    apply (G.degree_pos_iff_exists_adj v).mpr
    cases walk with
    | nil => exact (diff rfl).elim
    | cons e _ => exact ⟨_,e⟩
  exact factor_two G ((reg v) ▸ pos) reg

theorem family (n) : 2 ≤ Fintype.card (Vertex n) ∧ (graph n).Connected ∧
    (graph n).Colorable 2 ∧ (graph n).IsRegularOfDegree (n+2) ∧
    vertexCliqueCover (graph n) = 2*n+3 ∧ lineDomination (graph n) = n+2 ∧
    minMaximalMatching (graph n) = n+2 := by
  let color : (graph n).Coloring Bool := Coloring.mk Prod.fst (fun e => e.1)
  have bip : (graph n).Colorable 2 := by simpa using color.colorable
  exact ⟨by rw [order]; omega,connected n,bip,regular n,clique_exact n,edge_exact n⟩

theorem fixed_degree_equality (n : ℕ) :
    (n+2) * vertexCliqueCover (graph n) = (2*(n+2)-1) * lineDomination (graph n) := by
  rw [clique_exact,(edge_exact n).1,Nat.mul_comm (n+2)]
  congr 1

/-- No smaller coefficient works even with a fixed additive allowance. -/
theorem sharp_affine (c A : ℚ) (hc : c < 2) : ∃ n : ℕ,
    c * lineDomination (graph n) + A < (vertexCliqueCover (graph n) : ℚ) := by
  have pos : 0 < 2-c := by linarith
  obtain ⟨n,hn⟩ := exists_nat_gt ((A+1)/(2-c))
  have gap := (div_lt_iff₀ pos).mp hn
  refine ⟨n,?_⟩
  rw [(edge_exact n).1,clique_exact]
  push_cast
  nlinarith

theorem row1957_false : 2 ≤ Fintype.card (Vertex 2) ∧ (graph 2).Connected ∧
    (graph 2).IsRegularOfDegree 4 ∧ vertexCliqueCover (graph 2) = 7 ∧
    lineDomination (graph 2) = 4 ∧
    ¬ (vertexCliqueCover (graph 2) : ℚ) ≤ (4/3 : ℚ) * lineDomination (graph 2) + 1 := by
  obtain ⟨hn,hc,_,hr,hθ,he,_⟩ := family 2
  exact ⟨hn,hc,hr,hθ,he,by rw [hθ,he]; norm_num⟩

#print axioms cover_of_vertex_cover
#print axioms catalogue_factor_two
#print axioms bipartite_degree_bound
#print axioms fixed_degree_equality
#print axioms family
#print axioms sharp_affine
#print axioms row1957_false
#print axioms Archive.edge_exact
#print axioms Archive.cover_exact
#print axioms Archive.released_witness

end RegularCliques1957
