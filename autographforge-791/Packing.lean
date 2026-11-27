import Bound
namespace CubicRainbow791
open SimpleGraph Finset TriangleMatching1078
/-- The induced-matching packing bound: if every edge touches at most one
designated edge, any line-graph dominating set must have at least as many
members as the number of designated edges. -/
theorem packing_lower {U I : Type*} [Fintype U] [Fintype I] (G : SimpleGraph U)
    [DecidableRel G.Adj] (M : I → G.edgeSet)
    (apart : ∀ (e : G.edgeSet) (i j : I),
      (∃ v, v ∈ e.val ∧ v ∈ (M i).val) → (∃ w, w ∈ e.val ∧ w ∈ (M j).val) → i=j) :
    Fintype.card I ≤ lineDomination G := by
  classical
  obtain ⟨D,sz,dom⟩ := EulerDom574.line_attained G
  have existsEdge (i : I) : ∃ e : ↥D, ∃ v, v ∈ e.val.val ∧ v ∈ (M i).val := by
    obtain ⟨e,he,hit⟩ := (dominates_iff G D).mp dom (M i)
    exact ⟨⟨e,he⟩,hit⟩
  choose pick hit using existsEdge
  have inj : Function.Injective pick := fun i j eq => apart (pick i).val i j (hit i) (eq ▸ hit j)
  simpa [sz] using Fintype.card_le_of_injective pick inj

end CubicRainbow791
