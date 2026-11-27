import Cover

namespace EdgeCover1531
open SimpleGraph Finset TriangleMatching1078 BullCover1125
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Transfer feasibility by the equivalence of edge sets. Both optimizers
then have exactly the same set of feasible cardinalities. -/
private theorem map_mem (f : G ≃g H) {e : G.edgeSet} {x : V} (h : x ∈ e.val) :
    f x ∈ (f.mapEdgeSet e).val := Sym2.mem_map.mpr ⟨x,h,rfl⟩

private theorem transfer_cover (f : G ≃g H) {k : ℕ}
    (h : ∃ P : Finset G.edgeSet, P.card = k ∧ Covers G P) :
    ∃ P : Finset H.edgeSet, P.card = k ∧ Covers H P := by
  obtain ⟨P,sz,hit⟩ := h
  refine ⟨P.map f.mapEdgeSet.toEmbedding,(card_map _).trans sz,?_⟩
  intro w
  obtain ⟨v,rfl⟩ := f.surjective w
  obtain ⟨e,he,hv⟩ := hit v
  exact ⟨_,mem_map.mpr ⟨e,he,rfl⟩,map_mem f hv⟩

private theorem transfer_dom (f : G ≃g H) {k : ℕ}
    (h : ∃ D : Finset G.edgeSet, D.card = k ∧ Dominates G.lineGraph D) :
    ∃ D : Finset H.edgeSet, D.card = k ∧ Dominates H.lineGraph D := by
  obtain ⟨D,sz,hit⟩ := h
  refine ⟨D.map f.mapEdgeSet.toEmbedding,(card_map _).trans sz,(dominates_iff H _).mpr ?_⟩
  intro e
  obtain ⟨t,rfl⟩ := f.mapEdgeSet.surjective e
  obtain ⟨s,hs,v,vs,vt⟩ := (dominates_iff G D).mp hit t
  exact ⟨_,mem_map.mpr ⟨s,hs,rfl⟩,f v,map_mem f vs,map_mem f vt⟩

theorem iso_optimizers (f : G ≃g H) : edgeCoverNumber G = edgeCoverNumber H ∧
    lineDomination G = lineDomination H := by
  constructor
  · apply congrArg sInf
    exact Set.ext (fun _ => ⟨transfer_cover f,transfer_cover f.symm⟩)
  · apply congrArg sInf
    exact Set.ext (fun _ => ⟨transfer_dom f,transfer_dom f.symm⟩)
end EdgeCover1531
