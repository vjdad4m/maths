import Factor
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace RegularCliques1957
open SimpleGraph Finset HallRainbow1121 TriangleMatching1078

/-- Each selected edge meets at most 2d−1 edges, counting itself once. -/
theorem count_edges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (reg : G.IsRegularOfDegree d) :
    G.edgeFinset.card ≤ (2*d-1)*lineDomination G := by
  classical
  obtain ⟨D,sz,dom⟩ := Nat.sInf_mem (s:={k | ∃ D : Finset G.edgeSet, D.card=k ∧ Dominates G.lineGraph D})
    ⟨_,univ,rfl,fun e => Or.inl (mem_univ e)⟩
  change D.card = lineDomination G at sz
  let touched (e : G.edgeSet) := G.incidenceFinset e.val.out.1 ∪ G.incidenceFinset e.val.out.2
  have small (e : G.edgeSet) : (touched e).card ≤ 2*d-1 := by
    let a := G.incidenceFinset e.val.out.1
    let b := G.incidenceFinset e.val.out.2
    have he : e.val ∈ a ∩ b := mem_inter.mpr
      ⟨(G.mem_incidenceFinset _ _).mpr ((G.edge_mem_incidenceSet_iff).mpr (Sym2.out_fst_mem _)),
       (G.mem_incidenceFinset _ _).mpr ((G.edge_mem_incidenceSet_iff).mpr (Sym2.out_snd_mem _))⟩
    have both : 0 < (a ∩ b).card := Finset.card_pos.mpr ⟨_,he⟩
    have n₁ : a.card = d := (G.card_incidenceFinset_eq_degree _).trans (reg _)
    have n₂ : b.card = d := (G.card_incidenceFinset_eq_degree _).trans (reg _)
    have total := card_union_add_card_inter a b
    change (a ∪ b).card ≤ 2*d-1
    omega
  have covered : G.edgeFinset ⊆ D.biUnion touched := by
    intro x hx
    let e : G.edgeSet := ⟨x,(G.mem_edgeFinset).mp hx⟩
    obtain ⟨f,hf,v,vf,ve⟩ := (dominates_iff G D).mp dom e
    have member : x ∈ G.incidenceFinset v := (G.mem_incidenceFinset _ _).mpr
      ((G.edge_mem_incidenceSet_iff (e:=e)).mpr ve)
    have repr : s(f.val.out.1,f.val.out.2) = f.val := f.val.out_eq
    rw [← repr] at vf
    refine mem_biUnion.mpr ⟨f,hf,mem_union.mpr ?_⟩
    rcases Sym2.mem_iff.mp vf with rfl|rfl
    · exact Or.inl member
    · exact Or.inr member
  calc
    G.edgeFinset.card ≤ (D.biUnion touched).card := card_le_card covered
    _ ≤ ∑ e ∈ D, (touched e).card := card_biUnion_le
    _ ≤ ∑ _ ∈ D, (2*d-1) := sum_le_sum fun e _ => small e
    _ = _ := by simp [sz,Nat.mul_comm]

/-- On positive d-regular bipartite graphs the sharp coefficient is 2−1/d.
The twin family attains equality for every d≥2, and K₂ attains it for d=1. -/
theorem bipartite_degree_bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (hd : 0 < d) (reg : G.IsRegularOfDegree d)
    (bip : G.Colorable 2) :
    d * vertexCliqueCover G ≤ (2*d-1) * lineDomination G := by
  classical
  obtain ⟨color⟩ := bip
  let S := univ.filter (fun x => color x = 0)
  have sides {x y : V} (h : G.Adj x y) : (x ∈ S ∧ y ∉ S) ∨ (x ∉ S ∧ y ∈ S) := by
    have bits : ∀ i j : Fin 2, i ≠ j → (i=0 ∧ j≠0) ∨ (i≠0 ∧ j=0) := by decide
    simpa [S] using bits _ _ (color.valid h)
  have left := cover_of_vertex_cover G hd reg S (fun _ _ h =>
    (sides h).elim (fun e => Or.inl e.1) (fun e => Or.inr e.2))
  have right := cover_of_vertex_cover G hd reg (univ \ S) (fun x y h => by
    rcases sides h with e|e
    · exact Or.inr (mem_sdiff.mpr ⟨mem_univ _,e.2⟩)
    · exact Or.inl (mem_sdiff.mpr ⟨mem_univ _,e.1⟩))
  have partition := card_sdiff_add_card_eq_card (s:=S) (t:=univ) (subset_univ S)
  rw [card_univ] at partition
  have half : 2*vertexCliqueCover G ≤ Fintype.card V := by omega
  have degreeSum := G.sum_degrees_eq_twice_card_edges
  simp only [reg.degree_eq,sum_const,card_univ,smul_eq_mul] at degreeSum
  have bound := Nat.mul_le_mul_right d half
  rw [degreeSum,Nat.mul_assoc] at bound
  have halfEdges : vertexCliqueCover G * d ≤ G.edgeFinset.card := by omega
  exact (Nat.mul_comm _ _ ▸ halfEdges).trans (count_edges G reg)

end RegularCliques1957
