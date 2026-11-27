import HallRainbow
import Row1078

namespace RegularCliques1957
open SimpleGraph Finset HallRainbow1121 TriangleMatching1078

/-- In a positive regular graph, every vertex cover yields a clique partition
with at most as many parts. Hall pairs the independent complement into the cover. -/
theorem cover_of_vertex_cover {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (pos : 0 < d) (reg : G.IsRegularOfDegree d)
    (S : Finset V) (hit : ∀ x y, G.Adj x y → x ∈ S ∨ y ∈ S) :
    vertexCliqueCover G ≤ S.card := by
  classical
  have demand (x : V) (hx : x ∉ S) : d ≤ (S.filter (G.Adj x)).card := by
    rw [← reg.degree_eq x, ← card_neighborFinset_eq_degree]
    apply card_le_card
    intro y hy
    have h := (G.mem_neighborFinset x y).mp hy
    exact mem_filter.mpr ⟨(hit x y h).resolve_left hx,h⟩
  have cap (x : V) (_ : x ∈ S) : ((G.neighborFinset x) \ S).card ≤ d :=
    (card_le_card sdiff_subset).trans (reg.degree_eq x).le
  obtain ⟨mate,inj,hm⟩ := match_outside G S pos demand cap
  exact Nat.sInf_le (cover_of_matching G S mate inj hm)

/-- The endpoints of any edge-dominating set form a vertex cover. -/
theorem factor_two {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (pos : 0 < d) (reg : G.IsRegularOfDegree d) :
    vertexCliqueCover G ≤ 2 * lineDomination G := by
  classical
  obtain ⟨D,sz,dom⟩ := Nat.sInf_mem (s:={k | ∃ D : Finset G.edgeSet,
      D.card = k ∧ Dominates G.lineGraph D})
    ⟨_,univ,rfl,fun e => Or.inl (mem_univ e)⟩
  change D.card = lineDomination G at sz
  let ends (e : G.edgeSet) := univ.filter (fun v : V => v ∈ e.val)
  let S := D.biUnion ends
  have incident {v : V} : v ∈ S ↔ ∃ e ∈ D, v ∈ e.val := by simp [S,ends]
  have hit (x y : V) (xy : G.Adj x y) : x ∈ S ∨ y ∈ S := by
    obtain ⟨e,he,z,ze,zxy⟩ := (dominates_iff G D).mp dom ⟨s(x,y),xy⟩
    rcases Sym2.mem_iff.mp zxy with rfl|rfl
    · exact Or.inl (incident.mpr ⟨e,he,ze⟩)
    · exact Or.inr (incident.mpr ⟨e,he,ze⟩)
  apply (cover_of_vertex_cover G pos reg S hit).trans
  calc
    S.card ≤ ∑ e ∈ D, (ends e).card := card_biUnion_le
    _ ≤ ∑ _ ∈ D, 2 := sum_le_sum (fun e _ => by
      obtain ⟨⟨a,b⟩,h⟩ := e.val.exists_rep
      have sub : ends e ⊆ {a,b} := by
        intro x hx
        have he := (mem_filter.mp hx).2
        rw [← h] at he
        simpa using he
      exact (card_le_card sub).trans (card_insert_le _ _ |>.trans (by simp)))
    _ = _ := by simp [sz,Nat.mul_comm]

end RegularCliques1957
